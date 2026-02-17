// Register Specl language with highlight.js (mdBook provides hljs globally)
hljs.registerLanguage("specl", function(hljs) {
    var KEYWORDS = {
        keyword:
            "module const var type action init invariant property fairness use require " +
            "if then else let in for func with view auxiliary " +
            "all any forall exists fix " +
            "always eventually leads_to enabled changes " +
            "weak_fair strong_fair Some None",
        built_in:
            "head tail len keys values powerset union_all",
        type: "Bool Nat Int String Set Seq Dict Option",
        literal: "true false",
        operator:
            "and or not implies iff union intersect diff subset_of in"
    };

    return {
        name: "Specl",
        aliases: ["specl"],
        keywords: KEYWORDS,
        contains: [
            hljs.C_LINE_COMMENT_MODE,
            hljs.C_BLOCK_COMMENT_MODE,
            hljs.QUOTE_STRING_MODE,
            hljs.C_NUMBER_MODE,
            {
                className: "title.function",
                begin: /(?:action|invariant|property|func)\s+/,
                end: /(?=\(|\{)/,
                excludeBegin: true,
                keywords: KEYWORDS
            },
            {
                className: "title.class",
                begin: /module\s+/,
                end: /$/,
                excludeBegin: true
            },
            {
                className: "operator",
                begin: /=>|<=>|==|!=|<=|>=|\+\+|\.\.|[+\-*/%<>|]/
            }
        ]
    };
});
