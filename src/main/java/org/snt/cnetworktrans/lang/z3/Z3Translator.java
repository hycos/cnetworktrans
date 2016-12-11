package org.snt.cnetworktrans.lang.z3;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.snt.cnetwork.core.Operation;
import org.snt.cnetwork.core.Node;
import org.snt.cnetwork.core.domain.BooleanRange;
import org.snt.cnetwork.core.domain.Range;
import org.snt.cnetworktrans.core.RegexParser;
import org.snt.cnetworktrans.exceptions.NotSupportedException;
import org.snt.cnetworktrans.lang.SmtEscape;
import org.snt.cnetworktrans.lang.SmtTranslator;
import org.snt.inmemantlr.tree.Ast;

import java.util.Stack;


public class Z3Translator extends SmtTranslator {

    final static Logger LOGGER = LoggerFactory.getLogger(Z3Translator.class);

    @Override
    public String translate() throws NotSupportedException {

        LOGGER.info("Translate to Z3");

        StringBuilder finalOut = new StringBuilder();

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

                finalOut.append("(declare-variable " + n.getLabel() + " " + type + ")\n");
            }


            if(n.isConstraint())
                doBacktrack(n);
        }

        finalOut.append("\n");

        for (Node n : cn.vertexSet()) {
            if(n.isConstraint()) {
                finalOut.append("(assert (= true " + this.vresolv.get(n) + " ))\n");
            }
        }


        finalOut.append("\n");
        finalOut.append("(check-sat)\n" + "(get-model)");

        return finalOut.toString();
    }

    @Override
    public Stack<String> getOperationTrans(Node op) throws NotSupportedException {

        Operation operation = null;

        Stack<String> ret = new Stack<String> ();

        if(op.isOperation()) {
            operation = (Operation)op;
        } else {
            return ret;
        }

        if(operation.getKind().isSanitizer()) {
            throw new NotSupportedException(operation.getKind().toString() + " not supported");
        }

        switch(operation.getKind()){
            case ADD:
                ret.push("+");
                break;
            case MATCHES:
                ret.push("RegexIn");
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
                ret.push("Length");
                break;
            case OR:
                ret.push("or");
                break;
            case AND:
                ret.push("and");
                break;
            case INDEXOF:
                ret.push("indexof");
                break;
            case IMPLIES:
                ret.push("implies");
                break;

            case NEQUALS:
            case BOOL_NEQUALS:
            case STR_NEQUALS:
            case NUM_NEQUALS:
                Range r0 = (Range)op.getRange();
                assert (r0 instanceof BooleanRange);
                BooleanRange br0 = (BooleanRange) r0;
                ret.push("=");
                if (br0.isAlwaysTrue()) {
                    ret.push("not");
                }
                break;
            case BOOL_EQUALS:
            case STR_EQUALS:
            case NUM_EQUALS:
            case EQUALS:
                Range r1 = (Range)op.getRange();
                assert (r1 instanceof BooleanRange);
                ret.push("=");
                BooleanRange br1 = (BooleanRange) r1;
                if (br1.isAlwaysFalse()) {
                    ret.push("not");
                }
                break;
            case NOT:
                ret.push("not");
                break;
            case SUBSTR:
                ret.push("Substring");
                break;
            case REPLACE:
                ret.push("Replace");
                break;
            case CONCAT:
                ret.push("Concat");
                break;
            case VALUEOF:
            case TOSTR:
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
            case VALUEOF:
            case TOSTR:
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
    public String translateRegex(Node n) {
        LOGGER.info(" translate regex " + n.getLabel());
        RegexParser rp = new RegexParser();
        Ast regex = rp.parse(SmtEscape.trimQuotes(n.getLabel()));

        Z3RegexSplitter splitter = new Z3RegexSplitter(regex);
        return splitter.process();
    }

    @Override
    protected String esc(String s) {
        return Z3Escape.escapeSpecialCharacters(s);
    }


}
