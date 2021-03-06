/*
 * cnetworktrans - translate constraint network to various output formats
 * Copyright (C) 2017 Julian Thome <julian.thome.de@gmail.com>
 *
 * cnetworktrans is licensed under the EUPL, Version 1.1 or – as soon
 * they will be approved by the European Commission - subsequent versions of the
 * EUPL (the "Licence"); You may not use this work except in compliance with the
 * Licence. You may obtain a copy of the Licence at:
 *
 * https://joinup.ec.europa.eu/sites/default/files/eupl1.1.-licence-en_0.pdf
 *
 * Unless required by applicable law or agreed to in writing, software distributed
 * under the Licence is distributed on an "AS IS" basis, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied.  See the Licence for the
 * specific language governing permissions and limitations under the Licence.
 */

package com.github.hycos.cnetworktrans.lang.cvc4;

import com.github.hycos.cnetwork.core.graph.Edge;
import com.github.hycos.cnetwork.core.graph.Node;
import com.github.hycos.cnetwork.core.graph.DefaultNodeKind;
import com.github.hycos.cnetwork.core.graph.Operation;
import com.github.hycos.cnetworktrans.exceptions.NotSupportedException;
import com.github.hycos.cnetworktrans.lang.SmtEscape;
import com.github.hycos.cnetworktrans.lang.SmtTranslator;
import com.github.hycos.regex2smtlib.Translator;
import com.github.hycos.regex2smtlib.translator.exception.FormatNotAvailableException;
import com.github.hycos.regex2smtlib.translator.exception.TranslationException;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.snt.inmemantlr.exceptions.ParseTreeProcessorException;

import java.util.List;
import java.util.Set;
import java.util.Stack;

import static com.github.hycos.cnetwork.core.graph.DefaultNodeKind.*;


public class CVC4Translator extends SmtTranslator {

    final static Logger LOGGER = LoggerFactory.getLogger(CVC4Translator.class);

    public CVC4Translator() {
    }


    public boolean ctxCheck(Node n, DefaultNodeKind kind) {
        for(int k = this.ctx.size() - 1; k>= 0; k-- ){
            if(this.ctx.get(k) == kind) {
                return true;
            }
        }
        return false;
    }


    @Override
    public String translate() throws NotSupportedException,
            ParseTreeProcessorException {
        StringBuilder finalOut = new StringBuilder();
        LOGGER.debug("translate");

        finalOut.append("(set-logic ALL)\n" +
                "(set-option :produce-models true)\n" +
                "(set-option :strings-exp true)\n");

        // first check variables
        for (Node n : cn.vertexSet()) {
            if (n.isVariable() && !n.isRegex()) {
                String type;
                if (n.isBoolean()) {
                    type = "Bool";
                } else if (n.isString()) {
                    type = "String";
                } else {
                    type = "Int";
                }
                finalOut.append("(declare-fun " + n.getShortLabel() + " () " + type + ")" +
                        "\n");
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
                finalOut.append("(assert " + this.vresolv.get(n) + " )\n");
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
        Stack<String> ret = new Stack<>();

        boolean conv = false;


        if (ctxCheck(op, MATCHES) && op.isString()) {

            LOGGER.debug("CHECK " + op.getLabel());
            // first parameters of Matches are always strings
            Set<Edge> incoming = cn.outgoingEdgesOf(op);
            if(incoming != null) {
                for (Edge e : incoming) {
                    if (e.getDestNode().getKind() == MATCHES &&
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

        LOGGER.debug("get Operation Trans " );
        Stack<String> ret = new Stack<>();

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
        switch(operation.getKind().getValue().toString().toUpperCase()){
            case "ADD":
                ret.push("+");
                break;
            case "MATCHES":
                ret.push("str.in.re");
                break;
            case "SUB":
                ret.push("-");
                break;
            case "SMALLER":
                ret.push("<");
                break;
            case "GREATER":
                ret.push(">");
                break;
            case "SMALLEREQ":
                ret.push("<=");
                break;
            case "GREATEREQ":
                ret.push(">=");
                break;
            case "LEN":
                ret.push("str.len");
                break;
            case "OR":
                ret.push("or");
                break;
            case "AND":
                ret.push("and");
                break;
            case "!=":
            case "NEQUALS":
            case "BOOL_NEQUALS":
            case "STR_NEQUALS":
            case "NUM_NEQUALS":
//                Range r0 = op.getRange();
//                assert (r0 instanceof BooleanRange);
//                BooleanRange br0 = (BooleanRange)r0;
//                ret.push("=");
//                if (br0.isAlwaysTrue()) {
//                    ret.push("not");
//                }
//                break;
                ret.push("=");

                //BooleanRange br1 = (BooleanRange) r1;
                //if (op.getDomain().isAlwaysTrue()) {
                    ret.push("not");
                //}
                break;
            case "==":
            case "=":
            case "BOOL_EQUALS":
            case "STR_EQUALS":
            case "NUM_EQUALS":
            case "EQUALS":

                //op.getDomain().setTrue();

                //Range r1 = op.getRange();
                //assert (r1 instanceof BooleanRange);
                ret.push("=");

                //BooleanRange br1 = (BooleanRange) r1;
                if (op.getDomain().isAlwaysFalse()) {
                    ret.push("not");
                }
                break;
            case "INDEXOF":
                ret.push("str.indexof");
                break;
            case "REPLACE":
                ret.push("str.collapse");
                break;
            case "TOINT":
                if(params.get(0).isString()) {
                    ret.push("str.to.int");
                }
                break;
            case "TOSTR":

                if(params.get(0).isNumeric()) {
                    ret.push("int.to.str");
                } else if(params.get(0).isString()) {
                    return ret;
                }

                if(ctxCheck(op, MATCHES)) {
                    if (this.ctx.peek() == DefaultNodeKind.TOSTR) {
                        ret.push("str.to.re");
                    }
                }

                break;
            case "SUBSTR":
                ret.push("str.substr");
                break;
            case "CONCAT":
                if(ctxCheck(op, MATCHES)) {
                    ret.push("re.++");
                    //wrapStringParams(op,false);
                } else {
                    ret.push("str.++");
                }
                break;
            case "SEARCH":
            case "EXTERNAL":
            case "TOUPPER":
            case "TOLOWER":
            case "STR_EQUALSIC":
            case "STR_NEQUALSIC":
            case "APACHE_ESCECMA":
            case "APACHE_ESCHTML":
            case "APACHE_UESCHTML":
            case "APACHE_ESCJSON":
            case "APACHE_ESCXML10":
            case "APACHE_ESCXML11":
            case "ESAPI_ESCDN":
            case "ESAPI_ESCHTML":
            case "ESAPI_ESCHTMLATTR":
            case "ESAPI_ESCLDAP":
            case "ESAPI_ESCSQL":
            case "ESAPI_ESCXML":
            case "ESAPI_ESCXMLATTR":
            case "ESAPI_ESCXPATH":
                throw new NotSupportedException(operation.getKind().toString() + " not supported");
        }

        return ret;
    }

    @Override
    protected boolean notTranslatable(Operation op) {

        switch(op.getKind().getValue().toUpperCase()) {
            case "SEARCH":
            case "EXTERNAL":
            case "TOUPPER":
            case "TOLOWER":
            case "STR_EQUALSIC":
            case "STR_NEQUALSIC":
            case "APACHE_ESCECMA":
            case "APACHE_ESCHTML":
            case "APACHE_UESCHTML":
            case "APACHE_ESCJSON":
            case "APACHE_ESCXML10":
            case "APACHE_ESCXML11":
            case "ESAPI_ESCDN":
            case "ESAPI_ESCHTML":
            case "ESAPI_ESCHTMLATTR":
            case "ESAPI_ESCLDAP":
            case "ESAPI_ESCSQL":
            case "ESAPI_ESCXML":
            case "ESAPI_ESCXMLATTR":
            case "ESAPI_ESCXPATH":
                return true;
        }
        return false;
    }



    @Override
    protected String translateRegex(Node n) throws ParseTreeProcessorException {

        LOGGER.debug(" translate regex " + n.getLabel());

        String rexp = "";
        try {
            rexp = Translator.INSTANCE.translate("cvc4", SmtEscape.trimQuotes(n
                    .getLabel
                            ()));
        } catch (FormatNotAvailableException | TranslationException e) {
            assert (false);
            e.printStackTrace();
        }

        return rexp;
    }

    @Override
    protected String esc(String s) {
        return CVC4Escape.escapeSpecialCharacters(s);
    }


}
