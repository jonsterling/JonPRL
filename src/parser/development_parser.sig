signature DEVELOPMENT_PARSER =
sig
  type world
  structure DevelopmentAst : DEVELOPMENT_AST

  val parse : world -> (world * DevelopmentAst.t list) CharParser.charParser
end
