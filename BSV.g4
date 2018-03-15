grammar BSV;

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
    LowerCaseIdentifier | 'default_clock' | 'default_reset' | 'enable' | 'module' | 'no_reset' | 'path' | 'port' | 'ready' | 'same_family' | EscapedOperator
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
    packageide '::' '*'
    | identifier ('(' '..' ')')?
    ;

importdecl :
    'import' importitem (',' importitem)* ';'
    ;
importitem :
    pkgname=upperCaseIdentifier '::' '*'
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
    attributeinstance* 'method' bsvtype name=lowerCaseIdentifier ('(' methodprotoformals? ')')? ';'
    ;
methodprotoformals :
    methodprotoformal (',' methodprotoformal)*
    ;
methodprotoformal :
    attributeinstance* bsvtype? name=lowerCaseIdentifier
    | attributeinstance* functionproto
    ;
subinterfacedecl :
    attributeinstance* 'interface' bsvtype lowerCaseIdentifier ';'
    ;
typedecl :
    typedefsynonym
    | typedefenum
    | typedefstruct
    | typedeftaggedunion
    ;
typedeftype :
    typeide typeformals?
    ;
typeformals :
    '#' '(' typeformal (',' typeformal)* ')'
    ;
typeformal :
    ('numeric')? 'type' typeide
    ;
typedefsynonym :
    'typedef' bsvtype typedeftype ';'
    | 'typedef' functionproto typedeftype ';'
    ;
typedefenum :
    'typedef' 'enum' '{' typedefenumelement (',' typedefenumelement)* '}' upperCaseIdentifier derives? ';'
    ;
typedefenumelement :
    upperCaseIdentifier '(' IntLiteral ':' IntLiteral ')?' ('=' IntLiteral)?
    | upperCaseIdentifier '(' IntLiteral ')?' ('=' IntLiteral)?
    | upperCaseIdentifier ('=' IntLiteral)?
    ;
typedefstruct :
    'typedef' 'struct' '{' (structmember)* '}' typedeftype derives? ';'
    ;
typedeftaggedunion :
    'typedef' 'union' 'tagged' '{' (unionmember)* '}' typedeftype derives? ';'
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
    'union' 'tagged' '{' (unionmember)* '}'
    ;
derives :
    'deriving' '(' typeclasside (',' typeclasside)* ')'
    ;
vardecl :
    attributeinstance* t=bsvtype varinit (',' varinit)*  ';' #VarBinding
    | attributeinstance* t=bsvtype var=lowerCaseIdentifier arraydims '<-' rhs=expression ';' #ActionBinding
    | attributeinstance* 'let' (lowerCaseIdentifier arraydims | ('{' lowerCaseIdentifier (',' lowerCaseIdentifier )* '}'))  (op=('='|'<-') rhs=expression)? ';' #LetBinding
    | attributeinstance* 'match' pattern op=('<-'|'=') rhs=expression ';' #PatternBinding
    ;
varinit :
    var=lowerCaseIdentifier arraydims ('=' rhs=expression)?
    ;
arraydims :
    ('[' expression ']')*
    ;
typeclassdecl :
    'typeclass' typeclasside typeformals provisos? typedepends? ';' overloadeddecl* 'endtypeclass' (':' typeclasside)?
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
    functionproto ';'
    | moduleproto
    | vardecl
    ;
tctype : bsvtype | functionproto ;
typeclassinstance :
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
    'module' ('[' modulecontext=bsvtype ']')? name=lowerCaseIdentifier
    (  ( ('#' '(' methodprotoformals ')' )? '(' attributeinstance * moduleinterface=bsvtype ')' )
     | ( '(' methodprotoformals? ')' ) )
    provisos? ';'
    ;
modulestmt :
    methoddef
    | moduleinst
    | subinterfacedef
    | ruledef
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
    'method' bsvtype? name=lowerCaseIdentifier ('(' methodformals? ')')? provisos? methodcond? ';' (stmt)* 'endmethod' (':' lowerCaseIdentifier)?
    | 'method' bsvtype? name=lowerCaseIdentifier ('(' methodformals? ')')? methodcond? '=' expression ';'
    ;
methodformals :
    methodformal (',' methodformal)*
    ;
methodformal :
    attributeinstance* bsvtype? name=lowerCaseIdentifier
    | attributeinstance* functionproto
    ;
methodcond :
    'if' '(' expression ')'
    ;
subinterfacedef :
    'interface' upperCaseIdentifier lowerCaseIdentifier ';' (interfacestmt)* 'endinterface' (':' lowerCaseIdentifier)?
    | 'interface' bsvtype? lowerCaseIdentifier '=' expression ';'
    ;
ruledef :
    attributeinstance* 'rule' name=lowerCaseIdentifier rulecond? ';' rulebody 'endrule' (':' lowerCaseIdentifier)?
    ;
rulecond :
    ('if')? '(' expression ')'
    ;
rulebody :
    stmt*
    ;
functiondef :
    attributeinstance* functionproto ';' (stmt)* 'endfunction' (':' lowerCaseIdentifier)?
    | functionproto '=' expression ';'
    ;
functionproto :
    'function' bsvtype? name=lowerCaseIdentifier ('(' methodprotoformals? ')')? provisos?
    ;
externcimport :
    'import' '"BDPI"' (lowerCaseIdentifier '=')? 'function' bsvtype lowerCaseIdentifier '(' externcfuncargs? ')' provisos? ';'
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
    | '(' typeide ('#' '(' bsvtype (',' bsvtype)* ')')? ')'
    | functionproto
    | typenat
    | '(' bsvtype ')'
    ;
typeide :
    (pkg=upperCaseIdentifier '::')? name=upperCaseIdentifier
    | var=lowerCaseIdentifier
    | 'SizeOf'
    ;
typenat :
    IntLiteral
    ;
expression :
      expression ('&&&' expression)+ #tripleandexpr
    | pred=expression '?' expression ':' expression #condexpr
    | expression 'matches' pattern #matchesexpr
    | 'case' '(' expression ')' 'matches'? caseexpritem* 'endcase' #caseexpr
    | binopexpr #operatorexpr
    ;

caseexpritem :
    ('default'
    | (pattern patterncond)
    | (exprprimary (',' exprprimary )* )) ':' body=expression ';'
    ;

patterncond :
    ('&&&' expression)*
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
    | (pkg=upperCaseIdentifier '::')? var=anyidentifier #varexpr
    | IntLiteral #intliteral
    | RealLiteral #realliteral
    | StringLiteral #stringliteral
    | '?' #undefinedexpr
    | ('valueOf'|'valueof') '(' bsvtype ')' #valueofexpr
    | 'return' expression #returnexpr
    | '{' expression (',' expression)* '}' #bitconcat
    | array=exprprimary '[' msb=expression (':' lsb=expression)? ']' #arraysub
    | fcn=exprprimary '(' (expression (',' expression)*)? ')' #callexpr
    | 'clocked_by' exprprimary #clockedbyexpr
    | 'reset_by' exprprimary #resetbyexpr
    | bsvtype '’' ( ('{' expression (',' expression)* '}' ) | ( '(' expression ')' ) ) #typeassertionexpr
    | tag=upperCaseIdentifier '{' memberbinds '}' #structexpr
    | 'tagged' tag=upperCaseIdentifier (('{' memberbinds '}')|exprprimary|) #taggedunionexpr
    | 'interface' bsvtype (';')? (interfacestmt)* 'endinterface' (':' typeide)? #interfaceexpr
    | attributeinstance* 'rules' (':' lowerCaseIdentifier)? (rulesstmt)* 'endrules' (':' lowerCaseIdentifier)? #rulesexpr
    | beginendblock #blockexpr
    | actionblock #actionblockexpr
    | actionvalueblock #actionvalueblockexpr
    | seqfsmstmt #seqfsmexpr
    | parfsmstmt #parfsmexpr
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
    attributeinstance* 'begin' (':' lowerCaseIdentifier)? (stmt)* 'end' (':' lowerCaseIdentifier)?
    ;
actionblock :
    attributeinstance* 'action' (':' lowerCaseIdentifier)? (stmt)* 'endaction' (':' lowerCaseIdentifier)?
    ;
actionvalueblock :
    'actionvalue' (':' lowerCaseIdentifier)? (stmt)* 'endactionvalue' (':' lowerCaseIdentifier)?
    ;
regwrite :
    lhs=lvalue '<=' rhs=expression
    ;

stmt :
     vardecl
    | varassign
    | functiondef
    | moduledef
    | ruledef
    | regwrite ';'
    | beginendblock
    | ifstmt
    | casestmt
    | forstmt
    | whilestmt
    | actionblock
    | actionvalueblock
    | expression ';'
    ;
ifstmt :
    'if' '(' expression ')' stmt ('else' stmt)?
    ;
casestmt :
    'case' '(' expression ')' casestmtitem* casestmtdefaultitem? 'endcase'
    | 'case' '(' expression ')' 'matches' casestmtpatitem* casestmtdefaultitem? 'endcase'
    ;
casestmtitem :
    expression (',' expression)* ':' stmt
    ;
casestmtpatitem :
    pattern patterncond ':' stmt
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
    foroldinit
    | fornewinit
    ;
foroldinit :
    simplevarassign (',' simplevarassign)*
    ;
simplevarassign :
    var=lowerCaseIdentifier '=' expression
    ;
fornewinit :
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
pattern :
    '.' var=lowerCaseIdentifier
    | '.*'
    | constantpattern
    | taggedunionpattern
    | structpattern
    | tuplepattern
    | '(' pattern ')'
    ;
constantpattern :
    IntLiteral
    | IntPattern
    | RealLiteral
    | StringLiteral
    | upperCaseIdentifier
    ;

IntLiteral : ([1-9][0-9]*)?('\''[hdob]?)?[0-9a-fA-F_]+ ;
IntPattern : ([1-9][0-9]*)?('\''[hdob]?)?[0-9a-fA-F_?]+ ;

RealLiteral : [0-9]+'.'[0-9]+ ;

StringLiteral : '"' (~ [\f\n\r\t"])* '"'
    ;
taggedunionpattern :
    'tagged' tag=upperCaseIdentifier pattern?
    ;
structpattern :
    'tagged' tag=upperCaseIdentifier '{' lowerCaseIdentifier ':' pattern (',' lowerCaseIdentifier ':' pattern)* '}'
    ;
tuplepattern :
    '{' pattern (',' pattern)* '}'
    ;
attributeinstance :
    '(*' attrspec (',' attrspec)* '*)'
    ;
attrspec :
    attrname=identifier ('=' expression)?
    ;
provisos :
    'provisos' '(' proviso (',' proviso)* ')'
    ;
proviso :
    (pkg=upperCaseIdentifier '::')? var=upperCaseIdentifier '#' '(' bsvtype (',' bsvtype)* ')'
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
    | 'default_clock' lowerCaseIdentifier? ( '(' portide? ')' (op=('='|'<-') expression )? )? ';'
    | 'default_reset' lowerCaseIdentifier? ( '(' portide? ')' (op=('='|'<-') expression )? )? ';'
    | 'input_clock' lowerCaseIdentifier? '(' (portide (',' attributeinstance* portide )? )? ')' (op=('='|'<-') expression )? ';'
    | 'input_reset' lowerCaseIdentifier? '(' portide? ')' bviportopt* (op=('='|'<-') expression )? ';'
    | 'output_clock' lowerCaseIdentifier '(' portide? (',' attributeinstance* portide )? ')' ';'
    | 'output_reset' lowerCaseIdentifier '(' portide? ')' bviportopt* ';'
    | 'method' portide? lowerCaseIdentifier ('(' ( portide (',' portide)*)? ')' )? bvimethodopt* ';'
    | 'port' portide bviportopt* op=('='|'<-') expression ';'
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

WS : [ \f\n\r\t]+ -> skip ;
ONE_LINE_COMMENT   : '//' .*? '\r'? '\n' -> channel (3) ;
INLINE_COMMENT : '/*' .*? '*/' -> channel (3) ;