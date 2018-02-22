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
    [\\][-A-Za-z0-9=+_*&^%$#@!~<>?/|]+
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
    attributeinstance* bsvtype name=lowerCaseIdentifier
    | functionproto
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
    typeide (typeformals)?
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
    | attributeinstance* 'let' (lowerCaseIdentifier | ('{' lowerCaseIdentifier (',' lowerCaseIdentifier )* '}'))  (op=('='|'<-') rhs=expression)? ';' #LetBinding
    | attributeinstance* 'match' pattern op=('='|'<-') rhs=expression ';' #PatternBinding
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
tctype : bsvtype | functionproto ;
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
    'module' modulecontext? name=lowerCaseIdentifier
    (  ( ('#' '(' methodprotoformals ')' )? '(' attributeinstance * bsvtype ')' )
     | ( '(' methodprotoformals ')' ) )
    provisos? ';'
    ;
modulecontext :
    '[' bsvtype ']'
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
    'if' '(' condpredicate ')'
    ;
subinterfacedef :
    'interface' upperCaseIdentifier lowerCaseIdentifier ';' (interfacestmt)* 'endinterface' (':' lowerCaseIdentifier)?
    | 'interface' bsvtype? lowerCaseIdentifier '=' expression ';'
    ;
ruledef :
    attributeinstance* 'rule' name=lowerCaseIdentifier rulecond? ';' stmt* 'endrule' (':' lowerCaseIdentifier)?
    ;
rulecond :
    ('if')? '(' condpredicate ')'
    ;
functiondef :
    attributeinstance* functionproto (( ';' (stmt)* 'endfunction' (':' lowerCaseIdentifier)? )
                                     |( '=' expression ';' ))
    ;
functionproto :
    'function' bsvtype? name=lowerCaseIdentifier ('(' methodprotoformals? ')')? (provisos)?
    ;
externcimport :
    'import' '"BDPI"' (lowerCaseIdentifier '=')? 'function' bsvtype lowerCaseIdentifier '(' (bigcfuncargs)? ')' (provisos)? ';'
    ;

bigcfuncargs :
    bigcfuncarg (',' bigcfuncarg)*
    ;
bigcfuncarg :
    bsvtype (lowerCaseIdentifier)?
    ;
varassign :
    lvalue op=('='|'<-') expression ';'
    | '{' lvalue (',' lvalue)* '}' op=('='|'<-') expression ';'
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
    | '(' functionproto ')'
    | typenat
    ;
typeide :
    (pkg=upperCaseIdentifier '::')? typename=upperCaseIdentifier
    | typevar=lowerCaseIdentifier
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
    | op=('+' | '-') unopexpr
    | exprprimary
    ;

exprprimary :
    '(' expression ')' #parenexpr
    | exprprimary '.' exprfield=lowerCaseIdentifier #fieldexpr
    | ( bsvtype | ( '(' bsvtype ')' ) ) '\'' exprprimary #castexpr
    | (pkg=upperCaseIdentifier '::')? anyidentifier #varexpr
    | IntLiteral #intliteral
    | RealLiteral #realliteral
    | StringLiteral #stringliteral
    | '?' #undefinedexpr
    | ('valueof' | 'valueOf') '(' bsvtype ')' #valueofexpr
    | 'return' expression #returnexpr
    | '{' expression (',' expression)* '}' #bitconcat
    | array=exprprimary  '[' expression (':' expression)? ']' #arraysub
    | fcn=exprprimary '(' (expression (',' expression)*)? ')' #callexpr
    | 'clocked_by' exprprimary #clockedbyexpr
    | 'reset_by' exprprimary #resetbyexpr
    | bsvtype '’' ( ( '{' expression (',' expression)* '}' ) | ( '(' expression ')' )) #typeassertion
    | tag=upperCaseIdentifier '{' memberbinds '}' #structexpr
    | 'tagged' upperCaseIdentifier (('{' memberbinds '}' ) | (exprprimary) | ) #taggedunionexpr
    | 'interface' bsvtype (';')? (interfacestmt)* 'endinterface' (':' typeide)? #interfaceexpr
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
    'begin' (':' lowerCaseIdentifier)? (stmt)* 'end' (':' lowerCaseIdentifier)?
    ;
actionblock :
    'action' (':' lowerCaseIdentifier)? (stmt)* 'endaction' (':' lowerCaseIdentifier)?
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
    'if' '(' condpredicate ')' stmt ('else' stmt)?
    ;
casestmt :
    'case' '(' expression ')' (casestmtitem)* (bigdefaultitem)? 'endcase'
    | 'case' '(' expression ')' 'matches' (casestmtpatitem)* (bigdefaultitem)? 'endcase'
    ;
casestmtitem :
    expression (',' expression)* ':' stmt
    ;
casestmtpatitem :
    pattern ('&&&' expression)* ':' stmt
    ;
bigdefaultitem :
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
    lowerCaseIdentifier '=' expression
    ;
fornewinit :
    bsvtype lowerCaseIdentifier '=' expression (',' simplevardeclassign)*
    ;
simplevardeclassign :
    bsvtype? lowerCaseIdentifier '=' expression
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