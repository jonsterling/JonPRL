signature BUILTINS =
sig
  structure Conv : CONV

  type operator
  val unfold : operator -> Conv.conv
end

