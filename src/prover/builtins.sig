signature BUILTINS =
sig
  structure Conv : CONV

  type label
  val unfold : label -> Conv.conv
end

