grammar BSV;

packagedef : 
       packagedecl packagestmt* endpackage? EOF
       | packagestmt* EOF
       ;

packagedecl : 'package' pkgname=upperCaseIdentifier ';'
    ;
endpackage : 'endpackage' ( ':' upperCaseIdentifier )?
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
EscapedOperator :
    [\\][-+!%^&*<>=|/]+
    ;
lowerCaseIdentifier :
    LowerCaseIdentifier | 'default_clock' | 'default_reset' | 'enable' | 'no_reset' | 'path' | 'port' | 'ready' | 'same_family' | EscapedOperator
    ;

upperCaseIdentifier :
    UpperCaseIdentifier | 'C' | 'CF' | 'SB'
    ;

identifier : lowerCaseIdentifier | upperCaseIdentifier ;
anyidentifier : lowerCaseIdentifier | upperCaseIdentifier | DollarIdentifier ;

exportdecl :
    'export' exportitem (',' exportitem)* ';'
    ;

exportitem :
    upperCaseIdentifier '::' '*'
    | identifier ('(' '..' ')')?
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
    | attributeinstance* t=type var=lowerCaseIdentifier arraydims '<-' rhs=expression ';' #ActionBinding
    | attributeinstance* 'let' (lowerCaseIdentifier | ('{' lowerCaseIdentifier (',' lowerCaseIdentifier )* '}'))  ('=' rhs=expression)? ';' #LetBinding
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
    attributeinstance* 'rule' rulename=lowerCaseIdentifier rulecond? ';' rulebody 'endrule' (':' lowerCaseIdentifier)?
    ;
rulecond :
    ('if')? '(' condpredicate ')'
    ;
rulebody :
    bigstmt*
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
    lvalue op=('='|'<-') expression ';'
    | '{' lvalue (',' lvalue)* '}' op=('='|'<-') expression ';'
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
       pred=expression '?' expression ':' expression #CondExpr
    |  expression 'matches' pattern #MatchesExpr
    | 'case' '(' expression ')' 'matches'? (caseexpritem)* (caseexprdefaultitem)? 'endcase' #CaseExpr
    | binopexpr '?' expression ':' expression #SimpleCondExpr
    | binopexpr #OperatorExpr
    ;

caseexpritem :
    pattern ('&&&' expression)* ':' expression ';'
    | expression (',' expression)* ':' expression ';'
    ;
caseexprdefaultitem :
    'default' (':')? expression ';'
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

exprprimary :
    '(' expression ')' #parenexpr
    | exprprimary '.' exprfield=lowerCaseIdentifier #fieldexpr
    | ( type | ( '(' type ')' ) ) '\'' exprprimary #castexpr
    | (pkg=upperCaseIdentifier '::')? anyidentifier #varexpr
    | IntLiteral #intliteral
    | RealLiteral #realliteral
    | StringLiteral #stringliteral
    | '?' #undefinedexpr
    | ('valueof' | 'valueOf') '(' type ')' #valueofexpr
    | 'return' expression #returnexpr
    | '{' expression (',' expression)* '}' #bitconcat
    | array=exprprimary  '[' expression (':' expression)? ']' #arraysub
    | fcn=exprprimary '(' (expression (',' expression)*)? ')' #callexpr
    | 'clocked_by' exprprimary #clockedbyexpr
    | 'reset_by' exprprimary #resetbyexpr
    | type '’' ( ( '{' expression (',' expression)* '}' ) | ( '(' expression ')' )) #typeassertion
    | tag=upperCaseIdentifier '{' memberbinds '}' #structexpr
    | 'tagged' upperCaseIdentifier (('{' memberbinds '}' ) | (exprprimary) | ) #taggedunionexpr
    | 'interface' type (';')? (interfacestmt)* 'endinterface' (':' typeide)? #interfaceexpr
    | attributeinstance* 'rules' (':' lowerCaseIdentifier)? (rulesstmt)* 'endrules' (':' lowerCaseIdentifier)?
      #rulesexpr
    | beginendblock #blockexpr
    | actionblock #actionblockexpr
    | actionvalueblock #actionvalueblockexpr
    | seqfsmstmt #seqfsmstmtexpr
    | parfsmstmt #parfsmstmtexpr
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
    | vardecl
    | varassign
    ;
rulesstmt :
    ruledef
    | expression
    ;
beginendblock :
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
    | beginendblock
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
    matchee=expression ('&&&' condpredicate)?
    ;
pattern :
    '.' lowerCaseIdentifier
    | '.*'
    | constantpattern
    | taggedunionpattern
    | structpattern
    | tuplepattern
    | '(' pattern ')'
    ;
constantpattern :
    IntLiteral
    | RealLiteral
    | StringLiteral
    | upperCaseIdentifier
    ;

IntLiteral : ([1-9][0-9]*)?('\''[hdob]?)?[0-9a-fA-F_?]+ ;

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
    identifier ('=' expression)?
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

importbvi :
    'import' '"BVI"' identifier '=' moduleproto modulestmt* bvistmt* bvischedule* 'endmodule' (':' identifier)?
    ;

bvistmt :
    'parameter' identifier '=' expression ';'
    | 'no_reset' ';'
    | 'default_clock' lowerCaseIdentifier? ( '(' identifier? ')' ('=' expression )? )? ';'
    | 'default_reset' lowerCaseIdentifier? ( '(' identifier? ')' ('=' expression )? )? ';'
    | 'input_clock' lowerCaseIdentifier? '(' (identifier (',' attributeinstance* identifier )? )? ')' ('=' expression )? ';'
    | 'input_reset' lowerCaseIdentifier? '(' identifier? ')' bviportopt* ('=' expression )? ';'
    | 'output_clock' lowerCaseIdentifier '(' identifier? (',' attributeinstance* identifier )? ')' ';'
    | 'output_reset' lowerCaseIdentifier '(' identifier? ')' bviportopt* ';'
    | 'method' identifier? lowerCaseIdentifier ('(' ( identifier (',' identifier)*)? ')' )? bvimethodopt* ';'
    | 'port' identifier bviportopt* '=' expression ';'
    | 'inout' identifier bviportopt* ( '(' identifier? ')' )? ( '=' expression ) ';'
    | 'ifc_inout' identifier bviportopt* ( '(' identifier? ')' )? ( '=' expression)? ';'
    | 'path' '(' identifier ',' identifier ')' ';' 
    | 'same_family' '(' identifier ',' identifier ')' ';' 
    | 'interface' upperCaseIdentifier lowerCaseIdentifier ';' bvistmt* 'endinterface'
    ;

bviportopt :
    'clocked_by' '(' attributeinstance* identifier ')'
    | 'reset_by' '(' attributeinstance* identifier ')'
    ;
bvimethodopt :
    'clocked_by' '(' identifier ')'
    | 'reset_by' '(' identifier ')'
    | 'ready' '(' attributeinstance* identifier ')'
    | 'enable' '(' attributeinstance* identifier ')'
    ;

bvimethodname :
    bvimethodname '.' identifier
    | identifier
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