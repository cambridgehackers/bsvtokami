grammar BSV;

@header {
package bsvtokami;
}

packagedef : 
       packagedecl packagestmt* endpackage? EOF
       | packagestmt* EOF
       ;

packagedecl : 'package' pkgname=packageide ';'
    ;
endpackage : 'endpackage' ( ':' pkgname=packageide )?
    ;

PPTOK : '`'[a-zA-Z0-9_]+ -> channel(2) ;

UpperCaseIdentifier :
    [A-Z][a-zA-Z0-9_]*
    ;
LowerCaseIdentifier :
    [a-z_][a-zA-Z0-9_]*
    ;
DollarIdentifier :
    [$][a-z][a-zA-Z0-9_$]*
    ;

EscapedOperator :
    [\\][-A-Za-z0-9=+_*&^%$#@!~<>?/|]+
    ;

lowerCaseIdentifier :
    LowerCaseIdentifier | EscapedOperator
    ;

upperCaseIdentifier :
    UpperCaseIdentifier
    ;

anyidentifier : lowerCaseIdentifier | upperCaseIdentifier ;

exportdecl :
    'export' exportitem (',' exportitem)* ';'
    ;

exportitem :
    packageide '::' '*'
    | anyidentifier ('(' '..' ')')?
    ;

importdecl :
    'import' (upperCaseIdentifier '::')+ '*' ';'
    ;
packagestmt :
    interfacedecl
    | typedefsynonym
    | typedefenum
    | typedefstruct
    | typedeftaggedunion
    | typeclassdecl
    | typeclassinstance
    | externcimport
    | varbinding
    | functiondef
    | moduledef
    | importdecl
    | exportdecl
    ;
packageide :
    upperCaseIdentifier
    ;
interfacedecl :
    attributeinstance* 'interface' typedeftype ';' (interfacememberdecl)* 'endinterface' (':' typeide)?
    ;
interfacememberdecl :
    methodproto
    | subinterfacedecl
    ;

methodproto :
    attributeinstance* 'method' bsvtype name=lowerCaseIdentifier ('(' methodprotoformals? ')')? provisos? ';'
    ;
methodprotoformals :
    methodprotoformal (',' methodprotoformal)*
    ;
methodprotoformal :
    attributeinstance* bsvtype? name=lowerCaseIdentifier
    ;
subinterfacedecl :
    attributeinstance* 'interface' bsvtype lowerCaseIdentifier ';'
    ;
typedeftype :
    typeide typeformals?
    ;
typeformals :
    '#' '(' typeformal (',' typeformal)* ')'
    ;
typeformal :
    numeric=('numeric'|'numeric')? 'type' typeide
    ;
typedefsynonym :
    attributeinstance* 'typedef' bsvtype typedeftype ';'
    ;
typedefenum :
    'typedef' 'enum' '{' typedefenumelement (',' typedefenumelement)* '}' upperCaseIdentifier derives? ';'
    ;
typedefenumelement :
    tag=upperCaseIdentifier '[' from=IntLiteral (':' to=IntLiteral)? ']' ('=' tagval=IntLiteral)?
    | tag=upperCaseIdentifier ('=' tagval=IntLiteral)?
    ;
typedefstruct :
    attributeinstance* 'typedef' 'struct' '{' (structmember)* '}' typedeftype derives? ';'
    ;
typedeftaggedunion :
    attributeinstance* 'typedef' 'union' 'tagged'? '{' (unionmember)* '}' typedeftype derives? ';'
    ;
structmember :
    bsvtype lowerCaseIdentifier ';'
    | subunion lowerCaseIdentifier ';'
    ;
unionmember :
    bsvtype upperCaseIdentifier ';'
    | substruct upperCaseIdentifier ';'
    | subunion upperCaseIdentifier ';'
    ;
substruct :
    'struct' '{' (structmember)* '}'
    ;
subunion :
    'union' 'tagged'? '{' (unionmember)* '}'
    ;
derives :
    'deriving' '(' typeide (',' typeide)* ')'
    ;
moduleinst:
    /* MIT BSV: "new" */
    attributeinstance* ('let' | t=bsvtype) var=lowerCaseIdentifier '=' 'new' rhs=expression ';'
    ;
varinit :
    var=lowerCaseIdentifier ('=' rhs=expression)?
    ;
varbinding :
    attributeinstance* ('let' | t=bsvtype) varinit (',' varinit)*  ';'
    ;
actionbinding:
    attributeinstance* ('let' | t=bsvtype) var=lowerCaseIdentifier ('[' arraydim=expression ']')? '<-' rhs=expression ';'
    ;
patternbinding:
    attributeinstance* 'match' pattern op=('<-'|'=') rhs=expression ';'
    ;
typeclassdecl :
    attributeinstance* 'typeclass' typeclasside typeformals provisos? typedepends? ';' overloadeddecl* 'endtypeclass' (':' typeclasside)?
    ;
typeclasside :
    upperCaseIdentifier
    ;
typedepends :
    'dependencies' '(' typedepend (',' typedepend)* ')'
    ;
typedepend :
    typelist 'determines' typelist
    ;
typelist :
    typeide
    | '(' typeide (',' typeide)* ')'
    ;
overloadeddecl :
    attributeinstance*
    ( functionproto ';'
    | moduleproto
    | varbinding )
    ;
tctype : bsvtype | functionproto ;
typeclassinstance :
    attributeinstance*
    'instance' typeclasside '#' '(' tctype (',' tctype)* ')' provisos? ';'
    overloadeddef* 'endinstance' (':' typeclasside)?
    ;
overloadeddef :
    varassign
    | functiondef
    | moduledef
    ;
moduledef :
    attributeinstance* moduleproto (modulestmt)* 'endmodule' (':' lowerCaseIdentifier)?
    ;
moduleproto :
/* MIT BSV module proto */
    'module' moduleinterface=bsvtype name=lowerCaseIdentifier '(' moduleprotoformals? ')' provisos? ';'
/* Classic BSV module proto */
    | 'module' name=lowerCaseIdentifier '(' moduleinterface=bsvtype ')' provisos? ';'
    | 'module' name=lowerCaseIdentifier '#' '(' moduleprotoformals? ')' '(' moduleinterface=bsvtype ')' provisos? ';'
    ;
moduleprotoformals :
    moduleprotoformal (',' moduleprotoformal)*
    ;
moduleprotoformal :
    attributeinstance* 'parameter'? bsvtype name=lowerCaseIdentifier
    ;
modulestmt :
    methoddef
    | moduledef
    | moduleinst
    | subinterfacedef
    | stmt
    ;
methoddef :
    'method' bsvtype? name=lowerCaseIdentifier ('(' methodformals? ')')? provisos? methodcond? ';' (stmt)* 'endmethod' (':' lowerCaseIdentifier)?
    | 'method' bsvtype? name=lowerCaseIdentifier ('(' methodformals? ')')? methodcond? '=' expression ';'
    ;
methodformals :
    methodformal (',' methodformal)*
    ;
methodformal :
    attributeinstance* bsvtype? name=lowerCaseIdentifier
    ;
methodcond :
    /* MIT BSV allows when, Classic BSV: if */
    ('when'|'if') '(' expression ')'
    ;
subinterfacedef :
    'interface' upperCaseIdentifier lowerCaseIdentifier ';' (interfacestmt)* 'endinterface' (':' lowerCaseIdentifier)?
    | 'interface' upperCaseIdentifier? lowerCaseIdentifier '=' expression ';'
    ;
ruledef :
    attributeinstance* 'rule' name=lowerCaseIdentifier rulecond? ';' stmt* 'endrule' (':' lowerCaseIdentifier)?
    ;
rulecond :
    /* MIT BSV allows when, Classic BSV: optional if */
    ('when'|'if'|) '(' expression ')'
    ;
functiondef :
    attributeinstance* functionproto ';' (stmt)* 'endfunction' (':' lowerCaseIdentifier)?
    | functionproto '=' expression ';'
    ;
functionproto :
    'function' bsvtype? name=lowerCaseIdentifier ('(' methodformals? ')')? provisos?
    ;
externcimport :
    'import' '"BDPI"' (lowerCaseIdentifier '=')? 'function' bsvtype lowerCaseIdentifier '(' externcfuncargs? ')' ';'
    ;

externcfuncargs :
    externcfuncarg (',' externcfuncarg)*
    ;
externcfuncarg :
    bsvtype lowerCaseIdentifier?
    ;
varassign :
    attributeinstance* lvalue op=('='|'<-') expression ';'
    | attributeinstance* '{' lvalue (',' lvalue)* '}' op=('='|'<-') expression ';'
    ;
lvalue :
    lowerCaseIdentifier
    | exprprimary '.' lowerCaseIdentifier
    | exprprimary '[' index=expression ']'
    | exprprimary '[' msb=expression ((':' lsb=expression) | ('+:' widthup=IntLiteral) | ('-:' widthdown=IntLiteral)) ']'
    ;
bsvtype :
    typeide ('#' '(' bsvtype (',' bsvtype)* ')')?
    | var=lowerCaseIdentifier
    | typenat
    | '(' bsvtype ')'
    ;
typeide :
    (pkg=upperCaseIdentifier '::')* name=upperCaseIdentifier
    | typevar=lowerCaseIdentifier
    ;
typenat :
    IntLiteral
    ;
expression :
      pred=expression '?' expression ':' expression #condexpr
    | expression 'matches' pattern patterncond* #matchesexpr
    | 'case' '(' expression ')' (('matches' caseexprpatitem+) | caseexpritem*) caseexprdefaultitem? 'endcase' #caseexpr
    | binopexpr #operatorexpr
    ;
caseexprpatitem :
    (pattern patterncond*) ':' body=expression ';'
    ;
caseexpritem :
    match=expression (',' altmatches=expression)*':' body=expression ';'
    ;
caseexprdefaultitem :
    'default' ':' body=expression ';'
    ;

patterncond :
    ('&&&' expression)
    ;
binopexpr :
       left=binopexpr op=('**' | '**') right=binopexpr
    |  left=binopexpr op=('*' | '/' | '%' | '**') right=binopexpr
    |  left=binopexpr op=('+' | '-') right=binopexpr
    |  left=binopexpr op=('<<' | '>>') right=binopexpr
    |  left=binopexpr op=('<' | '<=' | '>' | '>=') right=binopexpr
    |  left=binopexpr op=('==' | '!=') right=binopexpr
    |  left=binopexpr op=('&' | '^' | '^~' | '~^') right=binopexpr
    |  left=binopexpr op=('|' | '|') right=binopexpr
    |  left=binopexpr op=('&&' | '&&&') right=binopexpr
    |  left=binopexpr op=('||' | '||') right=binopexpr
    | unopexpr
    ;
unopexpr : 
     op=('!' | '~' | '&' | '~&' | '|' | '~|' | '^' | '^~' | '~^') exprprimary
    | op=('+' | '-') right=exprprimary
    | exprprimary
    ;
exprprimary :
    '(' expression ')' #parenexpr
    | exprprimary '.' field=anyidentifier #fieldexpr
    | ( bsvtype | ( '(' bsvtype ')' ) ) '\'' exprprimary #castexpr
    | (pkg=upperCaseIdentifier '::')* var=lowerCaseIdentifier #varexpr
    | IntLiteral #intliteral
    | RealLiteral #realliteral
    | StringLiteral #stringliteral
    | '?' #undefinedexpr
    | ('valueOf'|'valueof') '(' bsvtype ')' #valueofexpr
    | '{' expression (',' expression)* '}' #bitconcat
    | array=exprprimary '[' msb=expression ((':' lsb=expression) | ('+:' widthup=IntLiteral) | ('-:' widthdown=IntLiteral))? ']' #arraysub
    | fcn=exprprimary '(' (expression (',' expression)*)? ')' #callexpr
    | 'when' '(' (expression (',' expression)*)? ')' #whenexpr
    | fcn=DollarIdentifier '(' (expression (',' expression)*)? ')' #syscallexpr
    | 'clocked_by' exprprimary #clockedbyexpr
    | 'reset_by' exprprimary #resetbyexpr
    | bsvtype '’' ( ('{' expression (',' expression)* '}' ) | ( '(' expression ')' ) ) #typeassertionexpr
    /* MIT BSV: optional tagged */
    | 'tagged'? (upperCaseIdentifier '::')* tag=upperCaseIdentifier (('{' memberbinds '}')|exprprimary|) #taggedunionexpr
    | 'interface' bsvtype (';')? (interfacestmt)* 'endinterface' (':' typeide)? #interfaceexpr
    | beginendblock #blockexpr
    | actionvalueblock #actionvalueblockexpr
    ;
memberbinds :
    memberbind (',' memberbind)*
    ;
memberbind :
    field=lowerCaseIdentifier ':' expression
    ;
interfacestmt :
    methoddef
    | subinterfacedef
    | varbinding
    | varassign
    ;
beginendblock :
    attributeinstance* 'begin' (':' lowerCaseIdentifier)? (stmt)* 'end' (':' lowerCaseIdentifier)?
    ;

/* MIT BSV does not need actionblock */
actionblock :
    attributeinstance* 'action' (stmt)* 'endaction'
    ;

/* MIT BSV does not need actionblock */
actionvalueblock :
    attributeinstance* 'actionvalue' (stmt)* 'endactionvalue'
    ;

regwrite :
    lhs=lvalue '<=' rhs=expression
    ;

stmt :
     varbinding
    | actionbinding
    | patternbinding
    | varassign
    | functiondef
    | ruledef
    | regwrite ';'
    | beginendblock
    | ifstmt
    | casestmt
    | forstmt
    | whilestmt
    | expression ';'
    | returnstmt
    | actionblock
    | actionvalueblock
    ;
ifstmt :
    'if' '(' expression ')' stmt ('else' stmt)?
    ;
/* MIT BSV: requires "matches" */
casestmt :
    'case' '(' expression ')' (('matches' casestmtpatitem+) | casestmtitem*) casestmtdefaultitem? 'endcase'
    ;
casestmtitem :
        match=expression (',' altmatches=expression)* ':' stmt
        ;
casestmtpatitem :
    pattern patterncond* ':' stmt
    ;
casestmtdefaultitem :
    'default' (':')? stmt
    ;
whilestmt :
    'while' '(' expression ')' stmt
    ;
forstmt :
    'for' '(' forinit ';' fortest ';' forincr ')' stmt
    ;
forinit :
    bsvtype var=lowerCaseIdentifier '=' expression (',' simplevardeclassign)*
    ;
simplevardeclassign :
    bsvtype? var=lowerCaseIdentifier '=' expression
    ;
fortest :
    expression
    ;
forincr :
    varincr (',' varincr)*
    ;
varincr :
    lowerCaseIdentifier '=' expression
    ;
returnstmt :
    'return' expression ';'
    ;
pattern :
    '.' var=lowerCaseIdentifier
    | '.*'
    | constantpattern
    | taggedunionpattern
    | tuplepattern
    | '(' pattern ')'
    ;
constantpattern :
    IntLiteral
    | IntPattern
    | RealLiteral
    | StringLiteral
    ;

IntLiteral : ([1-9][0-9]*)?('\''[hdob]?)?[0-9a-fA-F_]+ ;
IntPattern : ([1-9][0-9]*)?('\''[hdob]?)?[0-9a-fA-F_?]+ ;

RealLiteral : [0-9]+'.'[0-9]+ ;

StringLiteral : '"' (~ [\f\n\r\t"])* '"'
    ;
taggedunionpattern :
    /* MIT BSV: optional "tagged" */
    'tagged'? tag=upperCaseIdentifier pattern?
    | tag=upperCaseIdentifier '{' lowerCaseIdentifier ':' pattern (',' lowerCaseIdentifier ':' pattern)* '}'
    ;
tuplepattern :
    '{' pattern (',' pattern)* '}'
    ;
attributeinstance :
    '(*' attrspec (',' attrspec)* '*)'
    ;
attrspec :
    attrname=anyidentifier ('=' expression)?
    ;
provisos :
    'provisos' '(' proviso (',' proviso)* ')'
    ;
proviso :
    (pkg=upperCaseIdentifier '::')? var=upperCaseIdentifier '#' '(' bsvtype (',' bsvtype)* ')'
    ;

WS : [ \f\n\r\t]+ -> skip ;
ONE_LINE_COMMENT   : '//' .*? '\r'? '\n' -> channel (3) ;
INLINE_COMMENT : '/*' .*? '*/' -> channel (3) ;
