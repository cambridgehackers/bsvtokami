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

anyidentifier : lowerCaseIdentifier | upperCaseIdentifier | DollarIdentifier ;

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
    attributeinstance* 'method' bsvtype name=lowerCaseIdentifier ('(' methodprotoformals? ')')? ';'
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
    attributeinstance* 'typedef' 'union' '{' (unionmember)* '}' typedeftype derives? ';'
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
    'union' '{' (unionmember)* '}'
    ;
derives :
    'deriving' '(' typeide (',' typeide)* ')'
    ;
varbinding :
    attributeinstance* ('let' | t=bsvtype) var=lowerCaseIdentifier '=' rhs=expression  ';'
    ;
actionbinding:
    attributeinstance* ('let' | t=bsvtype) var=lowerCaseIdentifier '<-' rhs=expression ';'
    ;
patternbinding:
    attributeinstance* 'match' pattern op=('<-'|'=') rhs=expression ';'
    ;
moduledef :
    attributeinstance* moduleproto (modulestmt)* 'endmodule' (':' lowerCaseIdentifier)?
    ;
moduleproto :
    'module' moduleinterface=bsvtype name=lowerCaseIdentifier '(' methodprotoformals? ')' ';'
    ;
modulestmt :
    methoddef
    | moduledef
    | moduleinst
    | subinterfacedef
    | stmt
    ;
moduleinst :
    attributeinstance* bsvtype lowerCaseIdentifier ':' moduleapp ';'
    ;
moduleapp :
    lowerCaseIdentifier ('(' moduleactualparamarg (',' moduleactualparamarg)* ')')?
    ;
moduleactualparamarg :
    'reset_by' expression
    | 'clocked_by' expression
    | expression
    ;
methoddef :
    'method' bsvtype? name=lowerCaseIdentifier ('(' methodformals? ')')? methodcond? ';' (stmt)* 'endmethod' (':' lowerCaseIdentifier)?
    | 'method' bsvtype? name=lowerCaseIdentifier ('(' methodformals? ')')? methodcond? '=' expression ';'
    ;
methodformals :
    methodformal (',' methodformal)*
    ;
methodformal :
    attributeinstance* bsvtype? name=lowerCaseIdentifier
    ;
methodcond :
    'when' '(' expression ')'
    ;
subinterfacedef :
    'interface' upperCaseIdentifier lowerCaseIdentifier ';' (interfacestmt)* 'endinterface' (':' lowerCaseIdentifier)?
    | 'interface' bsvtype? lowerCaseIdentifier '=' expression ';'
    ;
ruledef :
    attributeinstance* 'rule' name=lowerCaseIdentifier rulecond? ';' stmt* 'endrule' (':' lowerCaseIdentifier)?
    ;
rulecond :
    'when' '(' expression ')'
    ;
functiondef :
    attributeinstance* functionproto ';' (stmt)* 'endfunction' (':' lowerCaseIdentifier)?
    | functionproto '=' expression ';'
    ;
functionproto :
    'function' bsvtype? name=lowerCaseIdentifier '(' methodprotoformals? ')'
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
    | lvalue '.' lowerCaseIdentifier
    | lvalue '[' index=expression ']'
    | lvalue '[' msb=expression ':' lsb=expression ']'
    ;
bsvtype :
    typeide ('#' '(' bsvtype (',' bsvtype)* ')')?
    | var=lowerCaseIdentifier
    | typenat
    | '(' bsvtype ')'
    ;
typeide :
    (pkg=upperCaseIdentifier '::')* name=upperCaseIdentifier
    ;
typenat :
    IntLiteral
    ;
expression :
      pred=expression '?' expression ':' expression #condexpr
    | expression 'matches' pattern #matchesexpr
    | 'case' '(' expression ')' 'matches' caseexpritem* caseexprdefaultitem? 'endcase' #caseexpr
    | binopexpr #operatorexpr
    ;

caseexpritem :
    (pattern patterncond*) ':' body=expression ';'
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
    |  left=binopexpr op=('&&' | '&&') right=binopexpr
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
    | exprprimary '.' field=lowerCaseIdentifier #fieldexpr
    | ( bsvtype | ( '(' bsvtype ')' ) ) '\'' exprprimary #castexpr
    | (pkg=upperCaseIdentifier '::')* var=lowerCaseIdentifier #varexpr
    | IntLiteral #intliteral
    | RealLiteral #realliteral
    | StringLiteral #stringliteral
    | '?' #undefinedexpr
    | ('valueOf'|'valueof') '(' bsvtype ')' #valueofexpr
    | '{' expression (',' expression)* '}' #bitconcat
    | array=exprprimary '[' msb=expression ((':' lsb=expression) | (':+' lsb=expression))? ']' #arraysub
    | fcn=exprprimary '(' (expression (',' expression)*)? ')' #callexpr
    | 'clocked_by' exprprimary #clockedbyexpr
    | 'reset_by' exprprimary #resetbyexpr
    | bsvtype '’' ( ('{' expression (',' expression)* '}' ) | ( '(' expression ')' ) ) #typeassertionexpr
    | (upperCaseIdentifier '::')* tag=upperCaseIdentifier (('{' memberbinds '}')|exprprimary|) #taggedunionexpr
    | 'interface' bsvtype (';')? (interfacestmt)* 'endinterface' (':' typeide)? #interfaceexpr
    | beginendblock #blockexpr
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
    ;
ifstmt :
    'if' '(' expression ')' stmt ('else' stmt)?
    ;
casestmt :
    'case' '(' expression ')' 'matches' casestmtpatitem* casestmtdefaultitem? 'endcase'
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
    tag=upperCaseIdentifier pattern?
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

WS : [ \f\n\r\t]+ -> skip ;
ONE_LINE_COMMENT   : '//' .*? '\r'? '\n' -> channel (3) ;
INLINE_COMMENT : '/*' .*? '*/' -> channel (3) ;
