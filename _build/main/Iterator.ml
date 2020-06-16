(***************************************************)
(*       ********* Iterator ************           *)
(*                                                 *)
(*                                                 *)
(*             Aleksandar Dimovski                 *)
(*          Mother Teresa Uni, Skopje              *)
(*                   2018 - 2019                   *)
(*                                                 *)
(***************************************************)

let abort = ref false
let compress = ref true (* false *)
let fmt = ref Format.std_formatter
let joinbwd = ref 2
let joinfwd = ref 2
let meetbwd = ref 2
let minimal = ref false
let refine = ref false
let retrybwd = ref 5
let start = ref 0.0
let stop = ref 0.0
let timebwd = ref false
let timefwd = ref false
let timeout = ref 300.0
let tracefwd = ref false
let tracebwd = ref false

exception Abort
exception Timeout
