signature SMALL_STEP =
sig
    type syn

    datatype t = STEP of syn | CANON
    exception Stuck of syn

    val step : syn -> t
end
