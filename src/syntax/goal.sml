structure Goal =
struct
  datatype class = MAIN | AUX
  datatype 'a goal = |: of class * 'a

  infix |:
  fun getGoal (_ |: g) = g

  fun toString f (c |: g) =
    case c of
         MAIN => "[main] " ^ f g
       | AUX => "[aux] " ^ f g
end
