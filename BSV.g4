grammar BSV;

packagedef : 
       packagedecl packagestmt* endpackage? EOF
       | packagestmt* EOF
       ;

packagedecl : 'package' packageide ';'
    ;
endpackage : 'endpackage' ( ':' packageide )?
    ;

UpperCaseIdentifier :
    [A-Z][a-zA-Z0-9_]*
    ;
LowerCaseIdentifier :
    [a-z_][a-zA-Z0-9_]*
    ;
DollarIdentifier :
    [$][a-z][a-zA-Z0-9_$]*
    ;

lowerCaseIdentifier :
    LowerCaseIdentifier | 'default_clock' | 'default_reset' | 'enable' | 'no_reset' | 'path' | 'port' | 'ready' | 'same_family'
    ;

upperCaseIdentifier :
    UpperCaseIdentifier | 'C' | 'CF' | 'SB'
    ;

exportdecl :
    'export' exportitem (',' exportitem)* ';'
    ;

exportitem :
    packageide '::' '*'
    | upperCaseIdentifier ('(' '..' ')')?
    | lowerCaseIdentifier ('(' '..' ')')?
    ;

importdecl :
    'import' importitem (',' importitem)* ';'
    ;
importitem :
    upperCaseIdentifier '::' '*'
    ;
packagestmt :
    interfacedecl
    | typedecl
    | typeclassdecl
    | typeclassinstance
    | externcimport
    | vardecl
    | functiondef
    | moduledef
    | importbvi
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
    attributeinstance* 'method' type lowerCaseIdentifier ('(' methodprotoformals? ')')? ';'
    ;
methodprotoformals :
    methodprotoformal (',' methodprotoformal)*
    ;
methodprotoformal :
    attributeinstance* type lowerCaseIdentifier
    | functionproto
    ;
subinterfacedecl :
    attributeinstance* 'interface' type lowerCaseIdentifier ';'
    ;
typedecl :
    typedefsynonym
    | typedefenum
    | typedefstruct
    | typedeftaggedunion
    ;
typedeftype :
    typeide (typeformals)?
    ;
typeformals :
    '#' '(' typeformal (',' typeformal)* ')'
    ;
typeformal :
    ('numeric')? 'type' typeide
    ;
typedefsynonym :
    'typedef' type typedeftype ';'
    | 'typedef' functionproto typedeftype ';'
    ;
typedefenum :
    'typedef' 'enum' '{' typedefenumelement (',' typedefenumelement)* '}' upperCaseIdentifier (derives)? ';'
    ;
typedefenumelement :
    upperCaseIdentifier '(' IntLiteral ':' IntLiteral ')?' ('=' IntLiteral)?
    | upperCaseIdentifier '(' IntLiteral ')?' ('=' IntLiteral)?
    | upperCaseIdentifier ('=' IntLiteral)?
    ;
typedefstruct :
    'typedef' 'struct' '{' (structmember)* '}' typedeftype (derives)? ';'
    ;
typedeftaggedunion :
    'typedef' 'union' 'tagged' '{' (unionmember)* '}' typedeftype (derives)? ';'
    ;
structmember :
    type lowerCaseIdentifier ';'
    | subunion lowerCaseIdentifier ';'
    ;
unionmember :
    type upperCaseIdentifier ';'
    | substruct upperCaseIdentifier ';'
    | subunion upperCaseIdentifier ';'
    ;
substruct :
    'struct' '{' (structmember)* '}'
    ;
subunion :
    'union' 'tagged' '{' (unionmember)* '}'
    ;
derives :
    'deriving' '(' typeclasside (',' typeclasside)* ')'
    ;
vardecl :
    attributeinstance* t=type varinit (',' varinit)*  ';' #VarBinding
    | attributeinstance*t=type var=lowerCaseIdentifier arraydims '<-' rhs=expression ';' #ActionBinding
    | attributeinstance* 'let' var=lowerCaseIdentifier arraydims ';' #LetDecl
    | attributeinstance* 'let' var=lowerCaseIdentifier arraydims '=' rhs=expression ';' #LetBinding
    | attributeinstance* 'let' var=lowerCaseIdentifier arraydims '<-' rhs=expression ';' #LetActionBinding
    | attributeinstance* 'match' pattern '<-' rhs=expression ';' #PatternActionBinding
    | attributeinstance* 'match' pattern '=' rhs=expression ';' #PatternBinding
    ;
varinit :
    var=lowerCaseIdentifier arraydims ('=' rhs=expression)?
    ;
arraydims :
    ('[' expression ']')*
    ;
typeclassdecl :
    'typeclass' typeclasside typeformals (provisos)? (typedepends)? ';' (overloadeddef)* 'endtypeclass' (':' typeclasside)?
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
overloadeddef :
    functionproto ';'
    | moduleproto
    | vardecl
    ;
tctype : type | functionproto ;
typeclassinstance :
    'instance' typeclasside '#' '(' tctype (',' tctype)* ')' (provisos)? ';'
    (varassign
    | functiondef
    | moduledef)* 'endinstance' (':' typeclasside)?
    ;
moduledef :
    attributeinstance* moduleproto (modulestmt)* 'endmodule' (':' lowerCaseIdentifier)?
    ;
moduleproto :
    'module' ('[' type ']')? modulename=lowerCaseIdentifier (moduleformalparams)? '(' (moduleformalargs)? ')' (provisos)? ';'
    ;
moduleformalparams :
    '#' '(' moduleformalparam (',' moduleformalparam)* ')'
    ;
moduleformalparam :
    attributeinstance* ('parameter')? type lowerCaseIdentifier
    | attributeinstance* ('parameter')? functionproto
    ;
moduleformalargs :
    attributeinstance* type
    | attributeinstance* type lowerCaseIdentifier (',' attributeinstance* type lowerCaseIdentifier)*
    ;
modulestmt :
    methoddef
    | moduleinst
    | subinterfacedef
    | ruledef
    | bigstmt
    ;
moduleinst :
    attributeinstance* type lowerCaseIdentifier ':' moduleapp ';'
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
    'method' (type)? lowerCaseIdentifier ('(' methodformals? ')')? provisos? (implicitcond)? ';' (bigstmt)* 'endmethod' (':' lowerCaseIdentifier)?
    | 'method' (type)? lowerCaseIdentifier ('(' methodformals? ')')? (implicitcond)? '=' expression ';'
    ;
methodformals :
    methodformal (',' methodformal)*
    ;
methodformal :
    attributeinstance* (type)? lowerCaseIdentifier
    | attributeinstance* functionproto
    ;
implicitcond :
    'if' '(' condpredicate ')'
    ;
subinterfacedef :
    'interface' upperCaseIdentifier lowerCaseIdentifier ';' (interfacestmt)* 'endinterface' (':' lowerCaseIdentifier)?
    | 'interface' (type)? lowerCaseIdentifier '=' expression ';'
    ;
ruledef :
    attributeinstance* 'rule' rulename=lowerCaseIdentifier (rulecond)? ';' rulebody 'endrule' (':' lowerCaseIdentifier)?
    ;
rulecond :
    ('if')? '(' condpredicate ')'
    ;
rulebody :
    (bigstmt)*
    ;
functiondef :
    attributeinstance* functionproto ';' (bigstmt)* 'endfunction' (':' lowerCaseIdentifier)?
    | functionproto '=' expression ';'
    ;
functionproto :
    'function' (type)? lowerCaseIdentifier ('(' functionformals? ')')? (provisos)?
    ;
functionformals :
    functionformal (',' functionformal)*
    ;
functionformal :
    (type)? lowerCaseIdentifier
    | functionproto
    ;
externcimport :
    'import' '"BDPI"' (lowerCaseIdentifier '=')? 'function' type lowerCaseIdentifier '(' (bigcfuncargs)? ')' (provisos)? ';'
    ;

bigcfuncargs :
    bigcfuncarg (',' bigcfuncarg)*
    ;
bigcfuncarg :
    type (lowerCaseIdentifier)?
    ;
varassign :
    lvalue '=' expression ';'
    | lvalue '<-' expression ';'
    ;
lvalue :
    lowerCaseIdentifier
    | lvalue '.' lowerCaseIdentifier
    | lvalue '[' expression ']'
    | lvalue '[' expression ':' expression ']'
    ;
type :
    typeprimary
    ;
typeprimary :
    typeide ('#' '(' type (',' type)* ')')?
    | '(' typeide ('#' '(' type (',' type)* ')')? ')'
    | '(' functionproto ')'
    | typenat
    ;
typeide :
    (pkg=upperCaseIdentifier '::')? upperCaseIdentifier
    | lowerCaseIdentifier
    | 'SizeOf'
    ;
typenat :
    IntLiteral
    ;
expression :
    '(' condpredicate ')' '?' expression ':' expression #CondExpr
    | binopexpr '?' expression ':' expression #SimpleCondExpr
    | binopexpr #OperatorExpr
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
    | op=('+' | '-') right=unopexpr
    | exprprimary
    ;

unop :
    '+'
    | '-'
    | '!'
    | '~'
    | '&'
    | '~&'
    | '|'
    | '~|'
    | '^'
    | '^~'
    | '~^'
    ;
binop :
    '*'
    | '|'
    | '%'
    | '+'
    | '-'
    | '<<'
    | '>>'
    | '<='
    | '>='
    | '<'
    | '>'
    | '=='
    | '!='
    | '&'
    | '^'
    | '^~'
    | '~^'
    | '|'
    | '&&'
    | '||'
    ;

exprprimary :
    '(' expression ')'
    | exprprimary '.' lowerCaseIdentifier
    | ( type | ( '(' type ')' ) ) '\'' exprprimary
    | (pkg=upperCaseIdentifier '::')? lowerCaseIdentifier
    | (pkg=upperCaseIdentifier '::')? upperCaseIdentifier
    | val=DollarIdentifier
    | val=IntLiteral
    | val=RealLiteral
    | val=StringLiteral
    | '?'
    | 'valueof' '(' type ')'
    | 'valueOf' '(' type ')'
    | 'return' expression
    | bitconcat
    | array=exprprimary  '[' expression (':' expression)? ']'
    | fcn=exprprimary '(' (expression (',' expression)*)? ')'
    | 'clocked_by' exprprimary
    | 'reset_by' exprprimary
    | typeassertion
    | structexpr
    | taggedunionexpr
    | interfaceexpr
    | rulesexpr
    | bigbeginendblock
    | actionblock
    | actionvalueblock
    | seqfsmstmt
    | parfsmstmt
    ;
bitconcat :
    '{' expression (',' expression)* '}'
    ;
typeassertion :
    type '’' bitconcat
    | type '’' '(' expression ')'
    ;
structexpr :
    tag=upperCaseIdentifier '{' memberbinds '}'
    ;
memberbinds :
    memberbind (',' memberbind)*
    ;
taggedunionexpr :
    'tagged' upperCaseIdentifier '{' memberbinds '}'
    | 'tagged' upperCaseIdentifier (exprprimary)?
    ;
memberbind :
    field=lowerCaseIdentifier ':' expression
    ;
interfaceexpr :
    'interface' type (';')? (interfacestmt)* 'endinterface' (':' typeide)?
    ;
interfacestmt :
    methoddef
    | subinterfacedef
    | vardecl
    | varassign
    ;
rulesexpr :
    attributeinstance* 'rules' (':' lowerCaseIdentifier)? (rulesstmt)* 'endrules' (':' lowerCaseIdentifier)?
    ;
rulesstmt :
    ruledef
    | expression
    ;
bigbeginendblock :
    'begin' (':' lowerCaseIdentifier)? (bigstmt)* 'end' (':' lowerCaseIdentifier)?
    ;
actionblock :
    'action' (':' lowerCaseIdentifier)? (bigstmt)* 'endaction' (':' lowerCaseIdentifier)?
    ;
actionvalueblock :
    'actionvalue' (':' lowerCaseIdentifier)? (bigstmt)* 'endactionvalue' (':' lowerCaseIdentifier)?
    ;
regwrite :
    lhs=expression '<=' rhs=expression
    ;

bigstmt :
     vardecl
    | varassign
    | functiondef
    | moduledef
    | ruledef
    | regwrite ';'
    | bigbeginendblock
    | bigif
    | bigcase
    | bigfor
    | bigwhile
    | actionblock
    | actionvalueblock
    | expression ';'
    ;
bigif :
    'if' '(' condpredicate ')' bigstmt ('else' bigstmt)?
    ;
bigcase :
    'case' '(' expression ')' (bigcaseitem)* (bigdefaultitem)? 'endcase'
    | 'case' '(' expression ')' 'matches' (bigcasepatitem)* (bigdefaultitem)? 'endcase'
    ;
bigcaseitem :
    expression (',' expression)* ':' bigstmt
    ;
bigcasepatitem :
    pattern ('&&&' expression)* ':' bigstmt
    ;
bigdefaultitem :
    'default' (':')? bigstmt
    ;
bigwhile :
    'while' '(' expression ')' bigstmt
    ;
bigfor :
    'for' '(' forinit ';' fortest ';' forincr ')' bigstmt
    ;
forinit :
    foroldinit
    | fornewinit
    ;
foroldinit :
    simplevarassign (',' simplevarassign)*
    ;
simplevarassign :
    lowerCaseIdentifier '=' expression
    ;
fornewinit :
    type lowerCaseIdentifier '=' expression (',' simplevardeclassign)*
    ;
simplevardeclassign :
    (type)? lowerCaseIdentifier '=' expression
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
condpredicate :
    condpredicate '&&&' condpredicate
    | expression 'matches' pattern
    | expression
    ;
pattern :
    '.' lowerCaseIdentifier
    | '.*'
    | constantpattern
    | taggedunionpattern
    | structpattern
    | tuplepattern
    ;
constantpattern :
    IntLiteral
    | RealLiteral
    | StringLiteral
    | upperCaseIdentifier
    ;

IntLiteral : ([1-9][0-9]*)?('\''[hdob]?)?[0-9a-fA-F_]+ ;

RealLiteral : [0-9]+'.'[0-9]+ ;

StringLiteral : '"' (~ [\n\r])* '"'
    ;
taggedunionpattern :
    'tagged' upperCaseIdentifier (pattern)?
    ;
structpattern :
    'tagged' upperCaseIdentifier '{' lowerCaseIdentifier ':' pattern (',' lowerCaseIdentifier ':' pattern)* '}'
    ;
tuplepattern :
    '{' pattern (',' pattern)* '}'
    ;
attributeinstance :
    '(*' attrspec (',' attrspec)* '*)'
    ;
attrspec :
    attrname ('=' expression)?
    ;
attrname :
    lowerCaseIdentifier
    | upperCaseIdentifier
    ;
provisos :
    'provisos' '(' proviso (',' proviso)* ')'
    ;
proviso :
    (pkg=upperCaseIdentifier '::')? var=upperCaseIdentifier '#' '(' type (',' type)* ')'
    ;
fsmstmt :
    regwrite ';'
    | expression ';'
    | actionblock
    | seqfsmstmt
    | parfsmstmt
    | iffsmstmt
    | whilefsmstmt
    | repeatfsmstmt
    | forfsmstmt
    | returnfsmstmt
    ;
seqfsmstmt :
    'seq' fsmstmt (fsmstmt)* 'endseq'
    ;
parfsmstmt :
    'par' fsmstmt (fsmstmt)* 'endpar'
    ;
iffsmstmt :
    'if' expression fsmstmt ('else' fsmstmt)?
    ;
returnfsmstmt :
    'return' ';'
    ;
whilefsmstmt :
    'while' '(' expression ')' loopbodyfsmstmt
    ;
forfsminit :
    regwrite
    | expression
    ;
forfsmstmt :
    'for' '(' forfsminit ';' expression ';' forfsminit ')' loopbodyfsmstmt
    ;
repeatfsmstmt :
    'repeat' '(' expression ')' loopbodyfsmstmt
    ;
loopbodyfsmstmt :
    fsmstmt
    | 'break' ';'
    | 'continue' ';'
    ;

portide : 
       (lowerCaseIdentifier|upperCaseIdentifier)
       ;

importbvi :
    'import' '"BVI"' portide '=' moduleproto modulestmt* bvistmt* bvischedule* 'endmodule' (':' (lowerCaseIdentifier|upperCaseIdentifier))?
    ;

bvistmt :
    'parameter' portide '=' expression ';'
    | 'no_reset' ';'
    | 'default_clock' lowerCaseIdentifier? ( '(' portide? ')' ('=' expression )? )? ';'
    | 'default_reset' lowerCaseIdentifier? ( '(' portide? ')' ('=' expression )? )? ';'
    | 'input_clock' lowerCaseIdentifier? '(' (portide (',' attributeinstance* portide )? )? ')' ('=' expression )? ';'
    | 'input_reset' lowerCaseIdentifier? '(' portide? ')' bviportopt* ('=' expression )? ';'
    | 'output_clock' lowerCaseIdentifier '(' portide? (',' attributeinstance* portide )? ')' ';'
    | 'output_reset' lowerCaseIdentifier '(' portide? ')' bviportopt* ';'
    | 'method' portide? lowerCaseIdentifier ('(' ( portide (',' portide)*)? ')' )? bvimethodopt* ';'
    | 'port' portide bviportopt* '=' expression ';'
    | 'inout' portide bviportopt* ( '(' portide? ')' )? ( '=' expression ) ';'
    | 'ifc_inout' portide bviportopt* ( '(' portide? ')' )? ( '=' expression)? ';'
    | 'path' '(' portide ',' portide ')' ';' 
    | 'same_family' '(' portide ',' portide ')' ';' 
    | 'interface' upperCaseIdentifier lowerCaseIdentifier ';' bvistmt* 'endinterface'
    ;

bviportopt :
    'clocked_by' '(' attributeinstance* portide ')'
    | 'reset_by' '(' attributeinstance* portide ')'
    ;
bvimethodopt :
    'clocked_by' '(' portide ')'
    | 'reset_by' '(' portide ')'
    | 'ready' '(' attributeinstance* portide ')'
    | 'enable' '(' attributeinstance* portide ')'
    ;

bvimethodname :
    bvimethodname '.' portide
    | portide
    ;

bvimethodnames :
    '(' bvimethodname (',' bvimethodname)* ')'
    | bvimethodname
    ;

bvischedule :
    'schedule' bvimethodnames ('CF' | 'SB' | 'C') bvimethodnames ';'
    ;

WS : [ \r\t\n]+ -> skip ;
ONE_LINE_COMMENT   : '//' .*? '\r'? '\n' -> channel (HIDDEN) ;
INLINE_COMMENT : '/*' .*? '*/' -> channel (HIDDEN) ;