signature CORE_CONV =
sig
  type conv

  val CID : conv
  val CTHEN : conv * conv -> conv

  val CFAIL : conv
  val CORELSE : conv * conv -> conv

  val CDEEP : conv -> conv
  val CTRY : conv -> conv
end

