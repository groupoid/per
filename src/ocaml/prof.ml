type entry = {
  mutable total_time : float;
  mutable call_count : int;
}

let stats : (string, entry) Hashtbl.t = Hashtbl.create 50
let active_start : (string, float) Hashtbl.t = Hashtbl.create 50
let stack = ref []
let profiling_enabled = ref false

let start_prof () = profiling_enabled := true
let stop_prof () = profiling_enabled := false

let get_time () = Sys.time ()

let measure name f =
  if not !profiling_enabled then f ()
  else begin
    let t0 = get_time () in
    let parent = match !stack with p::_ -> Some p | [] -> None in
    stack := name :: !stack;
    
    let result = try f () with e -> 
      stack := List.tl !stack;
      raise e 
    in
    
    let t1 = get_time () in
    let diff = t1 -. t0 in
    stack := List.tl !stack;
    
    let entry = try Hashtbl.find stats name with Not_found ->
      let e = { total_time = 0.0; call_count = 0 } in
      Hashtbl.add stats name e;
      e
    in
    entry.total_time <- entry.total_time +. diff;
    entry.call_count <- entry.call_count + 1;
    
    result
  end

let print_prof () =
  let sorted = Hashtbl.fold (fun k v acc -> (k, v) :: acc) stats []
               |> List.sort (fun (_, a) (_, b) -> compare b.total_time a.total_time)
  in
  let max_time = match sorted with (_, e)::_ -> e.total_time | [] -> 1.0 in
  
  Printf.printf "\nOCaml Profile Results:\n";
  List.iter (fun (name, entry) ->
    let bar_len = int_of_float (entry.total_time /. max_time *. 40.0) in
    let bar = String.make bar_len '=' ^ String.make (40 - bar_len) ' ' in
    Printf.printf "%-50s [%s] %.6fs (x%d)\n" name bar entry.total_time entry.call_count
  ) sorted;
  Printf.printf "\n"
