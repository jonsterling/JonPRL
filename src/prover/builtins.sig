signature BUILTINS =
sig
  structure Syntax : ABT
  structure Conv : CONV
    where type term = Syntax.t

  type label

  val unfold : label -> Conv.conv
end

