(* Compiled with Ocaml 4.07 *)
open Formulas
open Graphs
include Printf


      
module CDCL =
  struct
    include Model
    include DepGraph

    type unit_ret = Decide | Conflict of clause | Implication of clause * literal                                                            

    let rec analyze_conflict (m : model) (dlits : literal list) (conflict : clause) (dg : graph) (lvl : int) : clause * int =
      (* level should be the largest level of a literal in the conflict clause which is not the current level *)
      (let lits = (filter (fun lit -> (get_lvl dg (var lit)) = lvl) conflict) in
       (if (length lits) = 1 then
          (if (lvl = 0) then ([],-1) else
             (let lit = (hd lits) in
              (let new_lvl = (fold_left (fun lvl' lit -> (max (get_lvl dg (var lit)) lvl')) 0 (remove1 lit conflict)) in
               (conflict, new_lvl))))
        else
          (match (find_opt (fun lit' -> (not (mem (negate lit') dlits))) lits) with
           | None -> raise (Implementation "Should not occur")
           | Some lit ->
              (let clause = (negate lit)::(get_in_literals dg (negate lit,lvl)) in
               (let conflict' = (resolve_pair conflict clause) in
                (analyze_conflict m dlits conflict' dg lvl))))))



    (* optimized version, because it is used so often *)
    let find_unit (m : model) (form : formula) : unit_ret =
      (let rec search_empty (clauses : clause list) (unit_clause : clause) (lit : literal)  =
         (match clauses with
          | [] -> (Implication (unit_clause,lit))
          | c::clauses' -> (match (instantiate_clause c m) with
                           | Some [] -> Conflict c
                           | _ -> (search_empty clauses' unit_clause lit)))
       in (let rec search_unit (clauses : clause list) =
             (match clauses with
              | [] -> Decide
              | c::clauses' -> (match (instantiate_clause c m) with
                                | Some [] -> Conflict c
                                | Some [lit] -> (search_empty clauses' c lit)
                                | _ -> (search_unit clauses')))
           in (search_unit form)))
      

    (* let find_unit (m : model) (form : formula) : unit_ret =
     *   (match (find_opt (fun clause -> ((lift_bool empty_clausep) (instantiate_clause clause m))) form) with
     *    | Some clause -> Conflict clause
     *    | None -> 
     *       (match (find_opt (fun clause -> ((lift_bool unit_clausep) (instantiate_clause clause m))) form) with
     *        | None -> Decide
     *        | Some clause ->
     *           (match (instantiate_clause clause m) with
     *            | Some [lit] -> Implication (clause, lit)
     *            | _ -> raise (Implementation "unit: unit_clausep incorrect")))) *)

      
    let rec bcp (m : model) (dlits : literal list) (form : formula) (dg : graph) (lvl : int) : model option =
      (match (find_unit m form) with
       | Decide -> (match (get_free_variable (map var m) form) with
                    | None -> (if (modelsp m form) then
                                 (Some m) else None)
                    | Some x -> (decide x m dlits form dg (lvl + 1)))
       | Conflict clause ->
          (let (conflict,backtrack_lvl) = (analyze_conflict m dlits clause dg lvl) in
           (if backtrack_lvl < 0 then
              None (* UNSAT *)
            else
              (backtrack_learn m dlits conflict form dg backtrack_lvl)))
       | Implication (clause, lit) -> 
          ((add_edges_to dg (map var (remove1 lit clause)) (lit,lvl));
           (bcp (lit :: m) dlits form dg lvl)))

    and backtrack_learn (m : model) (dlits : literal list) (conflict : clause) (form : formula) (dg : graph) (lvl : int) : model option =
      (let dlits' = (nth_tl dlits ((length dlits) - lvl)) in
       (let i = (index m (nth dlits (((length dlits) - lvl) - 1))) in
        (let m' = (nth_tl m (i + 1)) in
         (let form' = (conjoin1 form conflict) in
          (reset dg lvl);
          (bcp m' dlits' form' dg lvl)))))

    and decide (x : int) (m : model) (dlits : literal list) (form : formula) (dg : graph) (lvl : int) : model option =
      (let lit = (Pos x) in
       (add_vertex dg (lit, lvl));
       (bcp (lit::m) (lit::dlits) form dg lvl))
  
    let cdcl (form : formula) : model option =
      (bcp (new_model()) [] form (new_graph()) 0)           
end;;
