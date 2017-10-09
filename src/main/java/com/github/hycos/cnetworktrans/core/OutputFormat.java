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

package com.github.hycos.cnetworktrans.core;


import com.github.hycos.cnetworktrans.lang.SmtTranslator;
import com.github.hycos.cnetworktrans.lang.cvc4.CVC4Translator;
import com.github.hycos.cnetworktrans.lang.s3.S3Translator;
import com.github.hycos.cnetworktrans.lang.sol.SolTranslator;
import com.github.hycos.cnetworktrans.lang.z3.Z3Translator;

public enum OutputFormat {

    SOL(0, "Sol"),
    CVC4 (1, "CVC4"),
    Z3STR2(2, "Z3Str2"),
    S3(3, "S3");


    private int id;
    private String name;
    private String grammar;

    OutputFormat(int id, String name) {
        this.id = id;
        this.name = name;
    }

    public SmtTranslator getTranslator() {
        switch (this) {
            case SOL: return new SolTranslator();
            case CVC4: return new CVC4Translator();
            case Z3STR2: return new Z3Translator();
            case S3: return new S3Translator();
        }
        return null;
    }

    public String getName() {
        return this.name;
    }

    public static OutputFormat getFormat(String desc) {
        switch(desc) {
            case "sol" : return SOL;
            case "cvc4" : return CVC4;
            case "z3str2": return Z3STR2;
            case "s3" : return S3;
        }
        return null;
    }

    public static String getAvailableFormats() {
        return "(" + SOL.getName() + "," + CVC4.getName() + "," + Z3STR2.getName() + "," + S3.getName() +")";
    }



}
