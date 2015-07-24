signature SNOC_VIEW =
sig
  type 'a telescope
  type label

  datatype ('a, 'r) view =
       Empty
     | Snoc of 'r * label * 'a

  val out : 'a telescope -> ('a, 'a telescope) view
  val into : ('a, 'a telescope) view -> 'a telescope
end

signature CONS_VIEW =
sig
  type 'a telescope
  type label

  datatype ('a, 'r) view =
       Empty
     | Cons of label * 'a * 'r

  val out : 'a telescope -> ('a, 'a telescope) view
  val outAfter : 'a telescope -> label -> ('a, 'a telescope) view
  val into : ('a, 'a telescope) view -> 'a telescope
end

signature LABEL =
sig
  include ORDERED

  val toString : t -> string
  val prime : t -> t
end

signature TELESCOPE =
sig
  type 'a telescope

  structure Label : LABEL
  type label = Label.t

  exception LabelExists

  (* smart constructors *)
  val empty : 'a telescope
  val snoc : 'a telescope -> label * 'a -> 'a telescope
  val cons : label * 'a -> 'a telescope -> 'a telescope

  val fresh : 'a telescope * label -> label

  (* lookup and search *)
  val lookup : 'a telescope -> label -> 'a
  val find : 'a telescope -> label -> 'a option
  val search : 'a telescope -> ('a -> bool) -> (label * 'a) option

  (* manipulation *)
  val map : 'a telescope -> ('a -> 'b) -> 'b telescope
  val mapAfter : 'a telescope -> label * ('a -> 'a) -> 'a telescope
  val modify : 'a telescope -> label * ('a -> 'a) -> 'a telescope
  val remove : 'a telescope -> label -> 'a telescope
  val interposeAfter : 'a telescope -> label * 'a telescope -> 'a telescope

  (* comparison *)
  val subtelescope : ('a * 'a -> bool) -> 'a telescope * 'a telescope -> bool
  val eq : ('a * 'a -> bool) -> 'a telescope * 'a telescope -> bool

  (* pretty printing *)
  val toString : ('a -> string) -> 'a telescope -> string

  (* These views may be used to lazily walk along a telescope *)
  structure SnocView : SNOC_VIEW
    where type 'a telescope = 'a telescope
    where type label = label

  structure ConsView : CONS_VIEW
    where type 'a telescope = 'a telescope
    where type label = label
end

signature TELESCOPE_NOTATION =
sig
  type 'a telescope
  type label

  val >: : 'a telescope * (label * 'a) -> 'a telescope
end

