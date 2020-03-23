(* Compiles with Ocaml 4.07 and 4.09 *)

(* implementation exceptions are errors *)
exception Implementation of string
exception Precondition of string

open Utility
                        
module Formula =
  struct
    include List
              
    type literal = Pos of int | Neg of int

    type clause = literal list

    type formula = clause list

    let negate (lit : literal) : literal =
      (match lit with
       | Pos n -> Neg n
       | Neg n -> Pos n)
      
    let empty_clausep (c : clause) : bool =
      (match c with
       | [] -> true
       | _ -> false)
        
    let unit_clausep (c : clause) : bool =
      (match c with
       | [_] -> true
       | _ -> false)

    let var (lit : literal) : int = (match lit with | Pos n -> n | Neg n -> n)

    let get_free_variable (bound : int list) (form : formula) : int option =
      (MyOption.bind 
         (find_opt (fun lit -> (not (mem (var lit) bound))) (flatten form))
         (fun x -> Some (var x)))
        
    let tautologyp (form : formula) : bool =
      (form = [])
      
    let disjoin (c1 : clause) (c2 : clause) : clause =
      (fold_right (fun lit c' -> (if (mem lit c') then c' else lit::c')) c1 c2)
                                                                                           
    let conjoin1 (cs : formula) (c : clause) : (clause list) = (c::cs)

    let conjoin (forms : formula list) : formula =
      (flatten forms)
                                                                 
    let resolve_pair (c1 : clause) (c2 : clause) : clause =
      (match (find_pair2 c1 c2 (fun x y -> (x = negate y))) with
       | None -> raise (Precondition "this should only be called on resolvable pairs")
       | Some (l1, l2) -> (disjoin (remove1 l1 c1) (remove1 l2 c2)))
                                      
    let pp_lit ppf (lit : literal)  =
      (Printf.fprintf ppf "%s%d" (match lit with | Pos n -> "" | Neg n -> "~") (var lit))

    let pp_clause ppf (clause : clause) =
      (List.iter (Printf.fprintf ppf "%a " pp_lit) clause)
    
    let pp_form ppf (form : formula) =
      (if (tautologyp form) then (Printf.fprintf ppf "True")
       else (List.iter (Printf.fprintf ppf "(%a) " pp_clause) form))
      
  end;;

module Model =
  struct
    include Formula
    type model = literal list
                         
    let value_opt (x : int) (m : model) : literal option =
      (find_opt (fun lit -> (var lit) = x) m)

    let (#::) (x : 'a) (xs : ('a list) option) : ('a list) option =
      (match xs with
       | None -> None
       | Some xs' -> (Some (x::xs')))


    (* alternative version *)
    (* let rec instantiate_clause (clause : clause) (m : model) : clause option = 
     *   (match m with
     *    | [] -> Some clause
     *    | lit::m' ->
     *       (match (find_opt (fun lit' -> (lit = lit')) clause) with
     *        | Some lit' -> None
     *        | None ->
     *           (let nlit = (negate lit) in
     *            (let clause' = (filter (fun lit' -> lit' <> nlit) clause) in
     *             (instantiate_clause clause' m'))))) *)

      
    let rec instantiate_clause (clause : clause) (m : model) : clause option =
      (match clause with
       | [] -> Some []
       | lit::clause' ->
          (match (value_opt (var lit) m) with
           | None -> lit #:: (instantiate_clause clause' m)
           | Some lit' -> (if (lit = lit') then None
                           else (instantiate_clause clause' m))))
       
    let rec instantiate_formula (form : formula) (m : model) : formula =
      (match form with
       | [] -> []
       | clause::form' -> (match (instantiate_clause clause m) with
                           | None -> (instantiate_formula form' m)
                           | Some clause' -> clause'::(instantiate_formula form' m)))
        
    let modelsp (m : model) (form : formula) : bool =
      (tautologyp (instantiate_formula form m))

    let new_model () = []
        
    let pp_model ppf (m : model) =
      (List.iter (Printf.fprintf ppf "%a " pp_lit) m)

  end;;
