signature DEVELOPMENT_PARSER =
sig
    structure Development : DEVELOPMENT
    structure DevelopmentAst : DEVELOPMENT_AST

    val parse : Development.t
                -> (Development.t * DevelopmentAst.t list)
                       CharParser.charParser
end
