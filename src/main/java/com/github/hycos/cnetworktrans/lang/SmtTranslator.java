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

package com.github.hycos.cnetworktrans.lang;

import com.github.hycos.cnetwork.api.NodeKindInterface;
import com.github.hycos.cnetwork.core.graph.ConstraintNetworkBuilder;
import com.github.hycos.cnetwork.core.graph.Node;
import com.github.hycos.cnetwork.core.graph.Operand;
import com.github.hycos.cnetwork.core.graph.Operation;
import com.github.hycos.cnetworktrans.exceptions.NotSupportedException;
import org.apache.commons.lang3.StringUtils;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.snt.inmemantlr.exceptions.ParseTreeProcessorException;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

public abstract class SmtTranslator {

    protected ConstraintNetworkBuilder cn = null;
    protected Map<Node, String> vresolv = null;
    protected Map<Node, String> vdecl = null;
    protected Stack<NodeKindInterface> ctx;


    final static Logger LOGGER = LoggerFactory.getLogger(SmtTranslator.class);

    public SmtTranslator() {
        this.vresolv = new HashMap<>();
        this.vdecl = new HashMap<>();
        this.ctx = new Stack<>();
    }

    public void init() {
        for(Node n : this.cn.vertexSet()) {
            LOGGER.debug("Node " + n.getLabel());
            if(n.isLiteral() || n.isRegex() || n.isOperand()) {
                this.vresolv.put(n, n.getLabel());
            }
        }
    }

    protected void doBacktrack(Node n) throws NotSupportedException, ParseTreeProcessorException {
        // we have to do it twice -- some functions need their params
        // to be converted
        backtrack(n);
    }

    protected void ctxPush(Node n) {
        if(n.isOperation())
            this.ctx.push(n.getKind());
    }

    protected void ctxPop(Node n) {
        if(n.isOperation())
            this.ctx.pop();
    }

    protected void backtrack(Node n) throws NotSupportedException, ParseTreeProcessorException {
        LOGGER.debug("backtrack " + n.getLabel());
        ctxPush(n);

        if (n.isRegex()) {
            this.vresolv.put(n, translateRegex(n));
            ctxPop(n);
            return;
        }

        List<Node> pars = this.cn.getParametersFor(n);

        if (pars != null && pars.size() > 0) {
            for(Node par : pars) {
                backtrack(par);
            }
        }


        if (!n.isOperation()) {

            Stack<String> otrans = getOperandTrans(n);
            int otsize = otrans.size();

            if(otsize > 0) {
                String out = "";

                out = otrans.pop();

                if(otsize == 2) {
                    while (!otrans.isEmpty()) {
                        out = "(" + otrans.pop() + " " + out;
                    }
                    out += StringUtils.repeat(")", otsize-1);
                }

                this.vresolv.put(n, out);
            }
            ctxPop(n);
            return;
        }


        Stack<String> strans = getOperationTrans(n);

        int stranssiz = strans.size();
        String out = "";

        while (!strans.isEmpty()) {
            out += "(" + strans.pop() + " ";
        }

        for (Node p : pars) {
            out += vresolv.get(p) + " ";
        }

        out += StringUtils.repeat(")",stranssiz);

        vresolv.put(n, out);
        ctxPop(n);
    }

    protected void debug() {

        LOGGER.debug("RESOLVE: =================================\n");
        for (Map.Entry<Node, String> e : vresolv.entrySet()) {
            LOGGER.debug(e.getKey().getId() + " :: " + e.getValue());
        }
        LOGGER.debug("\n=========================================\n");
    }

    public void setConstraintNetworkBuilder(ConstraintNetworkBuilder cn) throws
            NotSupportedException{
        if(!isTranslatable(cn)) {
            throw new NotSupportedException("Constraint Network is not translatable ");
        }
        this.cn = cn;
        init();
    }

    public abstract String translate() throws NotSupportedException, ParseTreeProcessorException;

    public abstract Stack<String> getOperationTrans(Node op) throws NotSupportedException;

    public Stack<String> getOperandTrans(Node op) throws NotSupportedException {

        Stack<String> ret = new Stack<String>();
        assert (op.isOperand());

        if (op.isLiteral() && op.isNumeric()) {
            Operand operand = (Operand) op;

            String lbl = "";

            //@TODO:Julian fix this -- we have to assume +1 dsize
            //NumRange nr = (NumRange) operand.getRange();

            //NumCut max = nr.getMax();
            if (operand.getDomain().isNegative()) {
                lbl = "(- " + (-Integer.parseInt(operand.getShortLabel())) + ")";
            } else {
                lbl = operand.getShortLabel();
            }
            ret.push(lbl);
            return ret;
        }

        String lbl = vresolv.get(op);

        if(op.isLiteral() && op.isString()) {
            lbl = SmtEscape.trimQuotes(lbl);
            lbl = "\"" +  esc(lbl) + "\"";
        }

        ret.push(lbl);
        return ret;
    }


    protected abstract boolean notTranslatable(Operation op);

    public boolean isTranslatable(ConstraintNetworkBuilder cn) {
        for(Node n : cn.vertexSet()) {
            if(n.isOperation()) {
                if(notTranslatable((Operation)n)) {
                    LOGGER.debug("op " + n.getKind());
                    return false;
                }
            }
        }
        return true;
    }

    protected abstract String translateRegex(Node regex) throws ParseTreeProcessorException;

    protected abstract String esc(String s);

}
