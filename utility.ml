

exception Error of string

(* for compatibility with 4.07 *)
module MyOption =
  struct                                         
    let bind (x : 'a option) (f : 'a -> 'b option) : 'b option =
      (match x with
       | None -> None
       | Some x' -> (f x'))
  end;;
       
module List =
  struct
    include List
              
    let rec remove1 x ls =
      (match ls with
       | [] -> []
       | a::ls' -> (if (x = a) then ls' else a::(remove1 x ls')))

    let rec find_pair2 (ls1 : 'a list) (ls2 : 'b list) (rel : 'a -> 'b -> bool) : ('a * 'b) option = 
      (match ls1 with
       | [] -> None
       | x::ls1' -> (match (find_opt (rel x) ls2) with
                     | None -> (find_pair2 ls1' ls2 rel)
                     | Some y -> Some (x,y)))

    let rec nth_tl (xs : 'a list) (i : int) : 'a list =
      (if i = 0 then xs
       else (nth_tl (tl xs) (i - 1)))

    let rec index (xs : 'a list) (x : 'a) : int =
      (match xs with
       | [] -> raise (Error "element not in list")
       | x'::xs' -> (if x = x' then 0 else (1 + (index xs' x))))
      
    let range i k : int list =
      (init k (fun x -> x + i))
  end;;      


module String =
  struct
    include String

    let explode (str : string) : char list =
      (List.init (length str) (get str))
  end;;
