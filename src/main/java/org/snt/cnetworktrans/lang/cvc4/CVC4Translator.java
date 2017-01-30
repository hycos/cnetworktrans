package org.snt.cnetworktrans.lang.cvc4;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.snt.cnetwork.core.Edge;
import org.snt.cnetwork.core.Node;
import org.snt.cnetwork.core.NodeKind;
import org.snt.cnetwork.core.Operation;
import org.snt.cnetwork.core.domain.BooleanRange;
import org.snt.cnetwork.core.domain.Range;
import org.snt.cnetworktrans.core.RegexParser;
import org.snt.cnetworktrans.exceptions.NotSupportedException;
import org.snt.cnetworktrans.lang.SmtEscape;
import org.snt.cnetworktrans.lang.SmtTranslator;
import org.snt.inmemantlr.exceptions.AstProcessorException;
import org.snt.inmemantlr.tree.Ast;

import java.util.List;
import java.util.Set;
import java.util.Stack;


public class CVC4Translator extends SmtTranslator {

    final static Logger LOGGER = LoggerFactory.getLogger(CVC4Translator.class);

    public CVC4Translator() {
    }


    public boolean ctxCheck(Node n, NodeKind kind) {
        for(int k = this.ctx.size() - 1; k>= 0; k-- ){
            if(this.ctx.get(k) == kind) {
                return true;
            }
        }
        return false;
    }


    @Override
    public String translate() throws NotSupportedException, AstProcessorException {
        StringBuilder finalOut = new StringBuilder();
        LOGGER.debug("translate");

        finalOut.append("(set-logic QF_S)\n" +
                "(set-option :produce-models true)\n" +
                "(set-option :strings-exp true)\n");

        // first check variables
        for (Node n : cn.vertexSet()) {
            if (n.isVariable()) {
                String type;
                if (n.isBoolean()) {
                    type = "Bool";
                } else if (n.isString()) {
                    type = "String";
                } else {
                    type = "Int";
                }
                finalOut.append("(declare-fun " + n.getLabel() + " () " + type + ")\n");
            }
            // backtrack starting from basic constraints
            if(n.isConstraint()) {
                LOGGER.debug("is constraint " + n.getLabel());
                doBacktrack(n);
            }
        }

        finalOut.append("\n");

        for (Node n : cn.vertexSet()) {
            if(n.isConstraint()) {
                finalOut.append("(assert (= true " + this.vresolv.get(n) + " ))\n");
            }
        }


        finalOut.append("\n");
        finalOut.append("(check-sat)\n" + "(get-model)");

        debug();
        assert(finalOut != null);
        assert(finalOut.toString() != null);

        LOGGER.debug("HEEELOO");

        return finalOut.toString();
    }

    @Override
    public Stack<String> getOperandTrans(Node op) throws NotSupportedException {
        Stack<String> ret = new Stack<String>();

        boolean conv = false;


        if (ctxCheck(op, NodeKind.MATCHES) && op.isString()) {

            LOGGER.info("CHECK " + op.getLabel());
            // first parameters of Matches are always strings
            Set<Edge> incoming = cn.outgoingEdgesOf(op);
            if(incoming != null) {
                for (Edge e : incoming) {
                    if (e.getDestNode().getKind() == NodeKind.MATCHES &&
                            e.getSequence() == 0) {
                        return ret;
                    }
                }
            }


            if (op.isOperand() && op.isString()) {
                // operand wrapped in conversion functions
                ret.push("str.to.re");
            }
        }

        ret.addAll(super.getOperandTrans(op));

        return ret;
    }

    @Override
    public Stack<String> getOperationTrans(Node op) throws NotSupportedException {

        LOGGER.info("get Operation Trans " );
        Stack<String> ret = new Stack<String>();

        Operation operation = null;

        if(op.isOperation()) {
            operation = (Operation)op;
        } else {
            return ret;
        }

        if(operation.getKind().isSanitizer()) {
            throw new NotSupportedException(operation.getKind().toString() + " not supported");
        }

        List<Node> params = this.cn.getParametersFor(op);
        LOGGER.debug("handle " + operation.getKind());
        switch(operation.getKind()){
            case ADD:
                ret.push("+");
                break;
            case MATCHES:
                ret.push("str.in.re");
                break;
            case SUB:
                ret.push("-");
                break;
            case SMALLER:
                ret.push("<");
                break;
            case GREATER:
                ret.push(">");
                break;
            case SMALLEREQ:
                ret.push("<=");
                break;
            case GREATEREQ:
                ret.push(">=");
                break;
            case LEN:
                ret.push("str.len");
                break;
            case OR:
                ret.push("or");
                break;
            case AND:
                ret.push("and");
                break;
            case NEQUALS:
            case BOOL_NEQUALS:
            case STR_NEQUALS:
            case NUM_NEQUALS:
                Range r0 = op.getRange();
                assert (r0 instanceof BooleanRange);
                BooleanRange br0 = (BooleanRange)r0;
                ret.push("=");
                if (br0.isAlwaysTrue()) {
                    ret.push("not");
                }
                break;
            case BOOL_EQUALS:
            case STR_EQUALS:
            case NUM_EQUALS:
            case EQUALS:
                Range r1 = op.getRange();
                assert (r1 instanceof BooleanRange);
                ret.push("=");
                BooleanRange br1 = (BooleanRange) r1;
                if (br1.isAlwaysFalse()) {
                    ret.push("not");
                }
                break;
            case INDEXOF:
                ret.push("str.indexof");
                break;
            case REPLACE:
                ret.push("str.replace");
                break;
            case VALUEOF:
                if(params.get(0).isString()) {
                    ret.push("str.to.int");
                }
                break;
            case TOSTR:

                if(params.get(0).isNumeric()) {
                    ret.push("int.to.str");
                } else if(params.get(0).isString()) {
                    return ret;
                }

                if(ctxCheck(op, NodeKind.MATCHES)) {
                    if (this.ctx.peek() == NodeKind.TOSTR) {
                        ret.push("str.to.re");
                    }
                }

                break;
            case SUBSTR:
                ret.push("str.substr");
                break;
            case CONCAT:
                if(ctxCheck(op, NodeKind.MATCHES)) {
                    ret.push("re.++");
                    //wrapStringParams(op,false);
                } else {
                    ret.push("str.++");
                }
                break;
            case SEARCH:
            case EXTERNAL:
            case TOUPPER:
            case TOLOWER:
            case STR_EQUALSIC:
            case STR_NEQUALSIC:
            case APACHE_ESCECMA:
            case APACHE_ESCHTML:
            case APACHE_UESCHTML:
            case APACHE_ESCJSON:
            case APACHE_ESCXML10:
            case APACHE_ESCXML11:
            case ESAPI_ESCDN:
            case ESAPI_ESCHTML:
            case ESAPI_ESCHTMLATTR:
            case ESAPI_ESCLDAP:
            case ESAPI_ESCSQL:
            case ESAPI_ESCXML:
            case ESAPI_ESCXMLATTR:
            case ESAPI_ESCXPATH:
                throw new NotSupportedException(operation.getKind().toString() + " not supported");
        }

        return ret;
    }

    @Override
    protected boolean notTranslatable(Operation op) {

        switch(op.getKind()) {
            case SEARCH:
            case EXTERNAL:
            case TOUPPER:
            case TOLOWER:
            case STR_EQUALSIC:
            case STR_NEQUALSIC:
            case APACHE_ESCECMA:
            case APACHE_ESCHTML:
            case APACHE_UESCHTML:
            case APACHE_ESCJSON:
            case APACHE_ESCXML10:
            case APACHE_ESCXML11:
            case ESAPI_ESCDN:
            case ESAPI_ESCHTML:
            case ESAPI_ESCHTMLATTR:
            case ESAPI_ESCLDAP:
            case ESAPI_ESCSQL:
            case ESAPI_ESCXML:
            case ESAPI_ESCXMLATTR:
            case ESAPI_ESCXPATH:
                return true;
        }
        return false;
    }



    @Override
    protected String translateRegex(Node n) throws AstProcessorException {

        assert(n.isRegex());
        //Ast regex = RegexParser.getInstance().parse(n.getLabel());
        RegexParser rp = new RegexParser();
        Ast regex = rp.parse(SmtEscape.trimQuotes(n.getLabel()));

        LOGGER.info(regex.toDot());

        String result = new CVC4RegexSplitter(regex).process();

        return result;
    }

    @Override
    protected String esc(String s) {
        return CVC4Escape.escapeSpecialCharacters(s);
    }


}
