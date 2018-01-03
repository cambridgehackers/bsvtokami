import java.util.*;

interface AST {
};

class Statement implements AST {
}

class Expression implements AST {
};

class Declaration extends Statement {
    List<Statement> statements;
    Declaration() {
	this.statements = new ArrayList<Statement>();
    }
    public void addStatement(Statement stmt) {
	statements.add(stmt);
    }
};

class RuleDef extends Declaration {
    public String name;
    public Expression guard;
    public RuleDef(String name) {
	super();
	this.name = name;
    }
}

class ModuleDef extends Declaration {
    String name;
    List<RuleDef> rules;
    public ModuleDef(String name) {
	super();
	this.name = name;
	this.rules = new ArrayList<RuleDef>();
    }
    public void addRule(RuleDef rule) {
	this.rules.add(rule);
    }
};

class OperatorExpression extends Expression {
    public OperatorExpression(String operator, Expression left) {
    }
    public OperatorExpression(String operator, Expression left, Expression Right) {
    }
}

class CondExpression extends Expression {
    public CondExpression(Expression condition, Expression thenExpr, Expression elseExpr) {
    }
};

class IntExpression extends Expression {
    public IntExpression(String value) {
    }
}
class RealExpression extends Expression {
    public RealExpression(String value) {
    }
}

class VectorRead extends Expression {
    public VectorRead(Expression vec, Expression index) {
    }
};

class StructRead extends Expression {
    public StructRead(Expression s, String field) {
    }
};

class VariableRead extends Expression {
    public VariableRead(String name) {
    }
};

class RegisterRead extends Expression {
    public RegisterRead(String name) {
    }
};

class LHS implements AST {
};

class Package extends Declaration {
    String name;
    public Package(String name) {
	super();
	this.name = name;
    }
};
