signature DEVELOPMENT_PARSER =
sig
    structure Development : DEVELOPMENT
    structure DevelopmentAst : DEVELOPMENT_AST

    val parse : Development.world
                -> (Development.world * DevelopmentAst.t list)
                       CharParser.charParser
end
