open Formulas
open Cdcl
include Printf
open Utility

module SudokuProblem9x9 =
  struct
    include Formula
    open Model
    include List
              
    (* represent unknowns by 0 *)
    type problem = (int list) list
        
    let new_problem (input : int list) : problem =
      (if (List.length input) <> 81 then
         raise (Implementation "Invalid input")
       else
         (let init9 = (range 0 9) in
          (map (fun i ->
               (map (fun j -> (List.nth input (i*9+j))) init9))
             init9)))

    let pp_row ppf (r : int list) =
      (fprintf ppf "|%i%i%i|%i%i%i|%i%i%i|\n"
         (nth r 0) (nth r 1) (nth r 2) (nth r 3) (nth r 4) (nth r 5) (nth r 6) (nth r 7) (nth r 8))
        
    let pp_problem ppf (p : problem) =
      (fprintf ppf "-------------\n%a%a%a-------------\n%a%a%a-------------\n%a%a%a-------------\n"
         pp_row (nth p 0) pp_row (nth p 1) pp_row (nth p 2)
         pp_row (nth p 3) pp_row (nth p 4) pp_row (nth p 5)
         pp_row (nth p 6) pp_row (nth p 7) pp_row (nth p 8))    
       
    let read_problems (filename : string) : problem list =
      (let in_chan = (open_in filename) in
       (let rec read_lines (in_chan) =
          (try
             (let line = (input_line in_chan) in
              line :: (read_lines in_chan))
           with eof ->
             (close_in in_chan); [])
        in (map new_problem
              (map (map (fun c -> Char.code c - 48))
                 (map String.explode (read_lines in_chan))))))


    (* convert an index for a variable over i,j,d injectively to an integer *)
    (* 0 <= x < 9
     * 0 <= y < 9
     * 1 <= d <= 9 *)
    let ind (x : int * int) (d : int) : int =
      (let (i,j) = x in
       (i * 9 + j) * 9 + (d - 1))

    (* compute the inverse of ind *)
    let ind_inv (k : int) : (int * int) * int =
      (let d0 = (k mod 9) in
       (let j = ((k - d0) / 9) mod 9 in
        (let i = ((((k - d0) / 9) - j) / 9) mod 9 in
         ((i,j),d0 + 1))))
        
    (* input should be list of svars of length 9 *)
    let valid (xs : (int * int) list) : formula =
      (if (length xs) <> 9 then
         raise (Implementation "invalid argument")
       else
         (conjoin
            (* 1 <= j <= 8  :  list of formulas *)
            (map (fun j ->
                 (conjoin
                    (* 0 <= i < j  :  list of formulas *)
                    (map (fun i ->
                         (* 1 <= d <= 9  :  formula *)
                         (map (fun d -> [(Neg (ind (nth xs i) d));
                                         (Neg (ind (nth xs j) d))]) (range 1 9)))
                       (range 0 j))))
               (range 1 8))))

      
    (* This is a constant *)
    let sudoku_form () =
      (conjoin [(conjoin (map (fun i ->
                              (valid (map (fun j -> (i,j)) (range 0 9))))
                            (range 0 9)));
                (conjoin (map (fun j ->
                              (valid (map (fun i -> (i,j)) (range 0 9))))
                            (range 0 9)));
                (conjoin (map (fun i ->
                              (conjoin
                                 (map (fun j ->
                                      (valid [(i,j); (i,j+1); (i,j+2);
                                              (i+1,j); (i+1,j+1); (i+1,j+2);
                                              (i+2,j); (i+2,j+1); (i+2,j+2)]))
                                    [0;3;6])))
                            [0;3;6]));
                (conjoin (map (fun i ->
                              (conjoin
                                 (map (fun j ->
                                      (conjoin
                                         (map (fun d ->
                                              (map (fun d' ->
                                                   [(Neg (ind (i,j) d));
                                                    (Neg (ind (i,j) d'))])
                                                 (range 1 (d - 1))))
                                            (range 1 8))))
                                    (range 0 9))))
                            (range 0 9)));
                (conjoin (map (fun i ->
                              (map (fun j ->
                                   (map (fun d -> (Pos (ind (i,j) d))) (range 1 9)))
                                 (range 0 9)))
                            (range 0 9)))
      ])
        
    let pp_su_lit ppf (lit : literal) =
      (let s = (match lit with
                | Neg x -> "~"
                | Pos x -> "") in
       (let ((i,j),l) = (ind_inv (var lit)) in
        (Printf.fprintf ppf "%s(%i,%i:%i)" s i j l)))

    let pp_su_clause ppf (clause : clause) =
      (List.iter (Printf.fprintf ppf "%a " pp_su_lit) clause)
        
    let pp_su_form ppf form =
      (if (tautologyp form) then (Printf.fprintf ppf "True")
       else (List.iter (Printf.fprintf ppf "(%a) " pp_su_clause) form))

        
    (* encode a sudoku problem into a formula by computing the model given by the specific problem *)
    let encode (p : problem) : formula =
      (let form = (sudoku_form() ) in
       (let p_mod = (flatten (map (fun (x,d) -> (map (fun d' -> (if d = d' then (Pos (ind x d'))
                                                                    else (Neg (ind x d')))) (range 1 9)))
                                   (filter (fun (_,d) -> d <> 0)
                                      (flatten (map (fun i -> (map (fun j -> ((i,j),(nth (nth p i) j))) (range 0 9))) (range 0 9)))))) in
        (let p_form = (map (fun lit -> [lit]) p_mod) in
         (conjoin [p_form; form]) 
      )))

    (* convert a model of positive literals back into a problem *)
    let convert (m : literal list) : problem =
      (map (fun i ->
           (map (fun j ->
                (match (find_opt (fun x -> (let ((i',j'),d) = (ind_inv (var x)) in
                                            i = i' && j = j')) m) with
                 | None -> 0
                 | Some x -> (snd (ind_inv (var x)))))
              (range 0 9)))
         (range 0 9))                      
  end;;



module Sudoku =
  struct
    include SudokuProblem9x9
    open Formulas

    let output_model (out : Model.model option) =
      (match out with
       | None -> printf "UNSAT!\n"
       | Some m ->
          (let pos_m = (filter (fun lit -> (match lit with Neg x -> false | Pos x -> true)) m) in
           printf "SAT with model: %a\n" pp_su_clause pos_m;
           (printf "Solution:\n%a" pp_problem (convert pos_m))))

    let run_problem problem =
      (let form = (encode problem) in
       (printf "Number of clauses: %i\n" (List.length form));
       (printf "%a" pp_problem problem);
       (print_endline "");
       (let tt = Sys.time() in
        (output_model (CDCL.cdcl form));
        (printf "Running time: %f s\n" (Sys.time() -. tt));
        (print_endline "")))
        
    let main () =
      (let problems = (read_problems "puzzles.sdk") in 
       (for i=0 to ((length problems) - 1) do
          (printf "Problem %i:\n" i);
          (run_problem (nth problems i))
        done;))
  end;;


Sudoku.main()
