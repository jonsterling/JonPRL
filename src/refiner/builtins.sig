signature BUILTINS =
sig
  structure Conv : CONV

  type label
  type operator
  val unfold : label -> operator * Conv.conv
end

