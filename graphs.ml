

exception GraphException of string

module DepGraph =
  struct
    include List
    open Formulas
    
    type vertex = (Formula.literal * int)
    type edge = vertex * vertex

    type graph = {mutable vertices : vertex list;
                  mutable edges : edge list}

    let lvl (v : vertex) : int = (snd v)
                   
    let src (e : edge) : vertex = (fst e)

    let tgt (e : edge) : vertex = (snd e)

    let new_graph () : graph =
      {vertices = []; edges = []}

    let add_vertex (g : graph) (v : vertex) : unit  =
      g.vertices <- v::g.vertices
      
    let add_edge (g : graph) (e : edge) : unit =
      g.edges <- e::g.edges

    let add_edges_to (g : graph) (xs : int list) (v : vertex) : unit =
      g.vertices <- v::g.vertices;
      (let es = (map (fun v' -> (v',v))
                   (filter (fun (x,_) -> (mem (Formula.var x) xs)) g.vertices)) in
       g.edges <- (append es g.edges))

    let reset (g : graph) (l : int) : unit =
      g.vertices <- (filter (fun v -> (lvl v) <= l) g.vertices);
      g.edges <- (filter (fun (s,t) -> ((lvl s) <= l) && (lvl t) <= l) g.edges)

    let get_in_literals (g : graph) (v : vertex) : (Formula.literal list) =
      (map (fun e -> (Formula.negate (fst (src e)))) (filter (fun (s,t) -> t = v) g.edges))

    let get_vertex (g : graph) (x : int) : vertex = (*(lit : Formula.literal) : vertex =*)
      (match (find_opt (fun (lit',_) -> (Formula.var lit') = x) g.vertices) with
       | None -> (raise (Implementation "Vertex undefined"))
       | Some v -> v)
         
    let get_lvl (g : graph) (x : int) : int = (*(lit : Formula.literal) : int =*)
      (lvl (get_vertex g x))
        
    let pp_vertex ppf (v : vertex) =
      (Printf.fprintf ppf "%a#%i " Formula.pp_lit (fst v) (lvl v))

    let pp_vertices ppf (vs : vertex list) =
      (List.iter (Printf.fprintf ppf "%a " pp_vertex) vs)
        
    let pp_edges ppf (es : edge list) =
      (List.iter (fun (s,t) -> (Printf.fprintf ppf "(%a,%a) " pp_vertex s pp_vertex t)) es)
        
    let pp_graph ppf (g : graph) =
      (Printf.fprintf ppf "({%a},{%a})" pp_vertices g.vertices pp_edges g.edges)
  end;;


