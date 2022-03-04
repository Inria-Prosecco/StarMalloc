module R = Random
module S = Set.Make(Int64)

let () =
  let n = ref 0 in
  let speclist =
    [("-n", Arg.Set_int n, "Number of elements")] in
  let usage_msg = "./binary -n $n" in
  Arg.parse speclist (fun _ -> ()) usage_msg;

  R.self_init ();
  let n = !n in
  let rds = Array.make n Int64.zero in
  for i = 0 to n-1 do
   Array.set rds i (R.int64 Int64.max_int)
  done;
  let rds2 = Array.to_list rds in
  let s = List.fold_left
    (fun a b -> S.add b a)
    S.empty rds2 in
  let n' = S.cardinal s in
  print_endline (string_of_int n');
  ()
