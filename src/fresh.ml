open Core
let fresh_var =
  let r = ref (-1) in
  fun () -> r := !r + 1; "x" ^ Int.to_string !r