package bsvtokami;

class ExpressionConverter extends BSVBaseVisitor<Expression>
{
        @Override
        public Expression visitIdentifier(BSVParser.IdentifierContext ctx) {
            return new VariableRead(ctx.getText());
        }
        @Override
        public Expression visitCondexpr(BSVParser.CondexprContext ctx) {
            return new CondExpression(visit(ctx.pred),
                                      visit(ctx.expression(1)),
                                      visit(ctx.expression(2)));
        }
        @Override public Expression visitBinopexpr(BSVParser.BinopexprContext ctx) {
            if (ctx.left == null) {
                return visit(ctx.unopexpr());
            } else {
                Expression left = visit(ctx.left);
                String op = ctx.op.getText();
                if (ctx.right != null) {
                    return new OperatorExpression(op, left, visit(ctx.right));
                } else {
                    return new OperatorExpression(op, left);
                }
            }
        }
        @Override public Expression visitUnopexpr(BSVParser.UnopexprContext ctx) {
            if (ctx.op != null) {
                String op = ctx.op.getText();
		return new OperatorExpression(op, visit(ctx.exprprimary()));
            } else {
                return visit(ctx.exprprimary());
            }
        }
    @Override public Expression visitIntliteral(BSVParser.IntliteralContext ctx) {
        return new IntExpression(ctx.IntLiteral().getText());
    }
    @Override public Expression visitRealliteral(BSVParser.RealliteralContext ctx) {
        return new RealExpression(ctx.RealLiteral().getText());
    }
}
