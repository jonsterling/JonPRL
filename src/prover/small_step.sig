signature SMALL_STEP =
sig
    type syn

    datatype t = STEP of syn | CANON | NEUTRAL
    exception Stuck of syn

    val step : syn -> t
end
