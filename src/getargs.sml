signature GETARGS = sig

  type 'a getarg = string -> 'a -> 'a

  val getReal   : real getarg
  val getBool   : bool getarg
  val getInt    : int getarg

  val getString : string getarg

  val getFlag : string -> bool

end

(** A call getReal s d looks for -s r in the command-line arguments and returns the value r on success. Otherwise, d is returned.

*)
