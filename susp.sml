structure Susp :> SUSP =
struct
  type 'a susp = unit -> 'a
  fun force t = t ()
  fun delay (t : 'a susp) =
    let
      exception Impossible

      val memo : 'a susp ref = ref (fn () => raise Impossible)

      fun t' () =
        let
          val r = t ()
        in
          memo := (fn () => r); r
        end
    in
      memo := t';
      fn () => (!memo)()
    end
  end
