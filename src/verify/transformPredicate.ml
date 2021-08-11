open Vlang
open Lang
open Vocab

(**********************************)
(**********************************)
(** Transform special predicates **)
(**********************************)
(**********************************)

let rec make_powerset : 'a list -> 'a list list
= fun lst ->
  match lst with
  | [] -> [[]]
  | hd::tl ->
    let ps = make_powerset tl in
    ps @ List.map (fun lst' -> hd::lst') ps

(* [p;q;r;s] => [(p,q); (q,r); (r,s)] *)
let rec make_pairs : 'a list -> ('a * 'a) list 
= fun lst ->
  match lst with
  | h1::h2::[] -> [(h1,h2)]
  | h1::h2::tl -> (h1,h2)::(make_pairs (h2::tl)) 
  | _ -> raise (Failure "make_pairs")

let remainder : vexp -> vexp
= fun mapvar ->
  let elemtyp = match (get_type_vexp mapvar) with Mapping (Address, t) -> t | _ -> assert false in
  let org_x = match mapvar with VVar v -> fst (org v) | _ -> assert false in
  VVar ("@R_"^org_x, elemtyp)

let make_elems : vexp -> ExpSet.t -> vexp -> vexp list
= fun mapvar addrs remainder ->
  ExpSet.fold (fun addr acc ->
    (Read (mapvar, addr, range_typ (get_type_vexp mapvar)))::acc
  ) addrs [remainder]

let make_elems2 : vexp -> vexp -> ExpSet.t -> vexp -> vexp list
= fun s mem addrs remainder ->
  ExpSet.fold (fun addr acc ->
    (Read (mem, Read (s, addr, range_typ (get_type_vexp s)), range_typ (get_type_vexp mem)))::acc
  ) addrs [remainder]

let rec make_sum_of_elems : vexp list -> vexp 
= fun lst ->
  match lst with
  | ve::[] -> ve (* when there does not exist addr expressions in the basic path *)
  | ve1::ve2::[] ->
    let (typ1,typ2) = (get_type_vexp ve1, get_type_vexp ve2) in
    let _ = assert (equal_typ typ1 typ2) in 
    VBinOp (VAdd,ve1,ve2,typ1) 
  | ve1::ve2::tl ->
    let (typ1,typ2) = (get_type_vexp ve1, get_type_vexp ve2) in
    let _ = assert (equal_typ typ1 typ2) in 
    let plus = VBinOp (VAdd,ve1,ve2,typ1) in
    make_sum_of_elems (plus::tl)
  | _ -> raise (Failure "make_sum_of_elems")

let add_safe : vexp -> vexp -> vformula
= fun ve1 ve2 ->
  let (typ1,typ2) = (get_type_vexp ve1, get_type_vexp ve2) in
  let _ = assert (equal_typ typ1 typ2) in 
  VBinRel (VGeq,VBinOp (VAdd, ve1, ve2, typ1), ve2) 

let rec all_elems_no_flow : vexp list -> vformula 
= fun lst ->
  match lst with
  | ve1::ve2::[] -> add_safe ve1 ve2
  | ve1::ve2::tl ->
    let (typ1,typ2) = (get_type_vexp ve1, get_type_vexp ve2) in
    let _ = assert (equal_typ typ1 typ2) in 
    let plus = VBinOp (VAdd,ve1,ve2,typ1) in
    VAnd (add_safe ve1 ve2, all_elems_no_flow (plus::tl)) 
  | _ -> raise (Failure "all_elems_no_flow") 

module PartitionSet = BatSet.Make (struct type t = ExpSet.t let compare = ExpSet.compare let to_string = string_of_set (string_of_set to_string_vexp) end) 

let rec f : ExpSet.t -> int -> PartitionSet.t list
= fun set k ->
  if k = 1 then [PartitionSet.singleton set] else
  if ExpSet.cardinal set = k then
    [ExpSet.fold (fun e acc ->
      PartitionSet.add (ExpSet.singleton e) acc
     ) set PartitionSet.empty] 
  else
    let e',set' = ExpSet.pop set in
    (* scenario: {{p,q}, {r,s}} *)
    (* if a new element is 'e', outputs {{p,q}, {r,s}, {e}} for each scenario. *)
    let case1 =
      List.map (fun partition_set -> PartitionSet.add (ExpSet.singleton e') partition_set) (f set' (k-1))
    in
    let case2 =
      List.fold_left (fun acc scenario -> (* partition scenario : {{p,q}, {r,s}} *)
        (* when existing scenario is {{p,q}, {r,s}}, outputs {{p,q,e'}, {r,s}} and {{p,q}, {r,s,e'}} *)
        PartitionSet.fold (fun partition acc' -> (* partition: {p,q} *)
          let replaced = PartitionSet.update partition (ExpSet.add e' partition) scenario in
          acc' @ [replaced]
        ) scenario acc
      ) [] (f set' k)
    in
    case1 @ case2

let rec upto set n =
  if n=1 then f set 1
  else (upto set (n-1)) @ (f set n)
  
let make_pre_eq : PartitionSet.t -> vformula 
= fun partition_set ->
  PartitionSet.fold (fun partition acc ->
    ExpSet.fold (fun e1 acc' ->
      ExpSet.fold (fun e2 acc'' ->
        if equal_ve e1 e2 then acc''
        else VAnd (acc'', VBinRel (VEq, e1, e2))
      ) partition acc'
    ) partition acc
  ) partition_set VTrue 

let make_pre_neq : PartitionSet.t -> vformula 
= fun partition_set ->
  let lst = PartitionSet.to_list partition_set in
  let cartesian = BatList.cartesian_product lst lst in
  List.fold_left (fun acc (partition1, partition2) ->
    if ExpSet.equal partition1 partition2 then acc
    else
      ExpSet.fold (fun e1 acc' ->
        ExpSet.fold (fun e2 acc'' ->
          VAnd (acc'', VNot (VBinRel (VEq, e1, e2)))
        ) partition2 acc'
      ) partition1 acc
  ) VTrue cartesian

let make_sum : vexp -> vexp -> PartitionSet.t -> vformula 
= fun ve mapvar partition_set ->
  let distinct_addrs = PartitionSet.fold (fun partition acc -> ExpSet.add (ExpSet.choose partition) acc) partition_set ExpSet.empty in
  let rem = remainder mapvar in
  let sum_of_elems = make_sum_of_elems (make_elems mapvar distinct_addrs rem) in
  VBinRel (VEq, ve, sum_of_elems)

let make_sigma_eq : vexp -> vexp -> ExpSet.t -> vformula
= fun ve mapvar addrs ->
  let rem = remainder mapvar in
  if ExpSet.is_empty addrs || ExpSet.cardinal addrs = 1 then
    VBinRel (VEq, ve, make_sum_of_elems (make_elems mapvar addrs rem))
  else
    let all_partitions = upto addrs (ExpSet.cardinal addrs) in
    List.fold_left (fun acc partition_set ->
      let pre_eq = make_pre_eq partition_set in
      let pre_neq = make_pre_neq partition_set in
      let sum = make_sum ve mapvar partition_set in 
      VAnd (acc, Imply (VAnd (pre_eq, pre_neq), sum))
    ) VTrue all_partitions

let make_sum_no_flow : vexp -> PartitionSet.t -> vformula
= fun mapvar partition_set ->
  let distinct_addrs = PartitionSet.fold (fun partition acc -> ExpSet.add (ExpSet.choose partition) acc) partition_set ExpSet.empty in
  let rem = remainder mapvar in
  let elems = make_elems mapvar distinct_addrs rem in
  all_elems_no_flow elems 

let make_no_flow : vexp -> ExpSet.t -> vformula
= fun mapvar addrs ->
  let org_x = match mapvar with VVar v -> fst (org v) | _ -> assert false in
  (* NOTE: propositional variables for remainders should not be renamed. They do not change. *)
  let remainder_no_flow = VBinRel (VEq, VVar ("@noflow_"^org_x, EType Bool), VCond VTrue) in
  let rem = remainder mapvar in
  if ExpSet.is_empty addrs then remainder_no_flow else
  if ExpSet.cardinal addrs = 1 then
    VAnd (all_elems_no_flow (make_elems mapvar addrs rem), remainder_no_flow)
  else
    let all_partitions = upto addrs (ExpSet.cardinal addrs) in
    let sum_no_flow =
      List.fold_left (fun acc partition_set ->
        let pre_eq = make_pre_eq partition_set in
        let pre_neq = make_pre_neq partition_set in
        let sum_no_flow = make_sum_no_flow mapvar partition_set in
        VAnd (acc, Imply (VAnd (pre_eq, pre_neq), sum_no_flow))
      ) VTrue all_partitions
    in
    VAnd (sum_no_flow, remainder_no_flow)

let rec get_addrs_f : var -> vformula -> ExpSet.t
= fun x vf ->
  match vf with
  | VTrue | VFalse -> ExpSet.empty
  | VNot f -> get_addrs_f x f
  | VAnd (f1,f2) -> ExpSet.union (get_addrs_f x f1) (get_addrs_f x f2)
  | VOr (f1,f2) -> ExpSet.union (get_addrs_f x f1) (get_addrs_f x f2)
  | VBinRel (_,e1,e2) -> ExpSet.union (get_addrs_e x e1) (get_addrs_e x e2)
  | Imply (f1,f2) -> ExpSet.union (get_addrs_f x f1) (get_addrs_f x f2)
  | SigmaEqual _ | NoOverFlow _ -> ExpSet.empty
  | ForAll (bvs,f) ->
    ExpSet.diff
      (get_addrs_f x f)
      (ExpSet.of_list (List.map (fun bv -> VVar bv) bvs))
  | Label (_,f) -> get_addrs_f x f

and get_addrs_e : var -> vexp -> ExpSet.t
= fun x ve ->
  match ve with
  | VInt _ -> ExpSet.empty
  | VVar _ -> ExpSet.empty
  | Read (VVar y, e2, _) when org x = org y -> ExpSet.singleton e2
  | Read (e1,e2,_) -> ExpSet.union (get_addrs_e x e1) (get_addrs_e x e2)
  | Write (VVar y, e2, e3) when org x = org y ->
    ExpSet.union (ExpSet.singleton e2) (get_addrs_e x e3)
  | Write (e1,e2,e3) ->
    ExpSet.union (get_addrs_e x e1) (ExpSet.union (get_addrs_e x e2) (get_addrs_e x e3))
  | VBinOp (_,e1,e2,_) -> ExpSet.union (get_addrs_e x e1) (get_addrs_e x e2)
  | VUnOp (_,e,_) -> get_addrs_e x e
  | VCast (_,e) -> get_addrs_e x e
  | VCond f -> get_addrs_f x f
  | Ite (e1,e2,e3) -> 
    ExpSet.union (get_addrs_e x e1) (ExpSet.union (get_addrs_e x e2) (get_addrs_e x e3))
  | Uninterp (fname,args,typ) ->
    List.fold_left (fun acc e -> ExpSet.union (get_addrs_e x e) acc) ExpSet.empty args

let rec get_id : vexp -> string -> string
= fun ve acc ->
  match ve with
  | VVar x ->
    if BatString.starts_with (fst x) "@" then acc
    else
      if acc = "" then fst (org x)
      else fst (org x) ^ "_" ^ acc
  | Read (e1,e2,_) -> get_id e2 (get_id e1 acc)
  | _ -> assert false

let trans_forall : vformula -> vformula
= fun vf ->
  match vf with
  | ForAll (bvs, VBinRel (VEq, ve, VInt n))
    when is_uint256 (get_type_vexp ve) && BatBig_int.equal n BatBig_int.zero ->
    let id = get_id ve "" in
    let elemtyp = get_type_vexp ve in
    let rem_zero = VBinRel (VEq, VVar ("@R_" ^ id, elemtyp), VInt BatBig_int.zero) in
    let rem_no_flow = VBinRel (VEq, VVar ("@noflow_" ^ id, EType Bool), VCond VTrue) in
    VAnd (vf, VAnd (rem_zero, rem_no_flow))
  | ForAll _ -> vf
  | _ -> assert false

let rec trans_f : vformula -> vformula -> vformula
= fun whole vf ->
  match vf with
  | VTrue | VFalse -> vf
  | VNot f -> VNot (trans_f whole f)
  | VAnd (f1,f2) -> VAnd (trans_f whole f1, trans_f whole f2)
  | VOr (f1,f2) -> VOr (trans_f whole f1, trans_f whole f2)
  | VBinRel (brel,e1,e2) -> vf
  | Imply (f1,f2) -> Imply (trans_f whole f1, trans_f whole f2)
  | SigmaEqual (x,e) ->
    let addrs = get_addrs_f x whole in
    make_sigma_eq e (VVar x) addrs
  | NoOverFlow x ->
    let addrs = get_addrs_f x whole in
    make_no_flow (VVar x) addrs
  | ForAll (bvs,f) -> trans_forall vf
  | Label (l,f) -> Label (l, trans_f whole f)

let transform : vformula -> vformula
= fun vf -> trans_f vf vf
