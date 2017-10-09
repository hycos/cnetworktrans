/*
* Inmemantlr - In memory compiler for Antlr 4
*
* Copyright 2016, Julian Thomé <julian.thome@uni.lu>
*
* Licensed under the EUPL, Version 1.1 or – as soon they will be approved by
* the European Commission - subsequent versions of the EUPL (the "Licence");
* You may not use this work except in compliance with the Licence. You may
* obtain a copy of the Licence at:
*
* https://joinup.ec.europa.eu/sites/default/files/eupl1.1.-licence-en_0.pdf
*
* Unless required by applicable law or agreed to in writing, software
* distributed under the Licence is distributed on an "AS IS" basis, WITHOUT
* WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
* See the Licence for the specific language governing permissions and
* limitations under the Licence.
*/

package com.github.hycos.cnetworktrans.lang;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class SmtEscape {

    final static Logger LOGGER = LoggerFactory.getLogger(SmtEscape.class);


    public static String trimQuotes(String s) {
        if(s == null || s.isEmpty())
            return "";

        StringBuilder out = new StringBuilder();

        char carr[] = s.toCharArray();

        for(int k = 0; k < carr.length; k ++) {
            char c = carr[k];
            if((k == 0 || k == carr.length - 1) && c == '\"') {
                continue;
            }
            out.append(c);
        }
        return out.toString();
    }

}