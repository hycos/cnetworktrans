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

package com.github.hycos.cnetworktrans.lang.sol;

import com.github.hycos.cnetwork.core.graph.Node;
import com.github.hycos.cnetwork.core.graph.Operation;
import com.github.hycos.cnetworktrans.exceptions.NotSupportedException;
import com.github.hycos.cnetworktrans.lang.SmtTranslator;

import java.util.Stack;


public class SolTranslator extends SmtTranslator {


    @Override
    public String translate() throws NotSupportedException {
        return this.cn.getConstraintNetwork().toConfig();
    }

    @Override
    public Stack<String> getOperationTrans(Node op) {
        return new Stack<>();
    }

    @Override
    protected boolean notTranslatable(Operation op) {
        return false;
    }


    @Override
    protected String translateRegex(Node regex) {
        return "";
    }

    @Override
    protected String esc(String s) {
        return s;
    }
}
