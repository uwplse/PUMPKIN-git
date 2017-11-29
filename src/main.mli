
val git_root: unit -> string

val git_path: string -> string

val retrieve: string -> string -> string -> in_channel

val splice: string -> int -> string list -> string -> unit

val line_of: string -> string -> int
