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

import com.github.hycos.cnetwork.api.labelmgr.exception.InconsistencyException;
import com.github.hycos.cnetwork.core.graph.ConstraintNetworkBuilder;
import com.github.hycos.cnetwork.core.graph.DefaultNodeKind;
import com.github.hycos.cnetwork.core.graph.Node;
import com.github.hycos.cnetwork.core.graph.Operand;
import com.github.hycos.cnetworktrans.core.OutputFormat;
import com.github.hycos.cnetworktrans.exceptions.NotSupportedException;
import com.github.hycos.cnetworktrans.lang.SmtEscape;
import com.github.hycos.cnetworktrans.lang.SmtTranslator;
import com.github.hycos.cnetworktrans.lang.cvc4.CVC4Escape;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.snt.inmemantlr.exceptions.ParseTreeProcessorException;

public class TestTranslators {

    final static Logger LOGGER = LoggerFactory.getLogger(TestTranslators.class);


    private static ConstraintNetworkBuilder cn = null;

    @BeforeAll
    public static void setUp() throws Exception {
        cn = new ConstraintNetworkBuilder();

        Operand a = new Operand("a", DefaultNodeKind.NUMVAR);
        Operand b = new Operand("b", DefaultNodeKind.NUMVAR);
        Operand c = new Operand("20", DefaultNodeKind.NUMLIT);

        Node add = cn.addOperation(DefaultNodeKind.ADD,a,b);
        Node smeq = cn.addConstraint(DefaultNodeKind.SMALLEREQ, add, c);


        Operand s = new Operand("s1", DefaultNodeKind.STRVAR);
        Operand ip = new Operand("a*", DefaultNodeKind.STRREXP);

        Node matches = cn.addConstraint(DefaultNodeKind.MATCHES, s, ip);

        Node len = cn.addOperation(DefaultNodeKind.LEN,s);

        Node lencon = cn.addConstraint(DefaultNodeKind.GREATEREQ, len, c);

        Node conv = cn.addOperation(DefaultNodeKind.TOSTR, a);

        Node matches2 = cn.addConstraint(DefaultNodeKind.MATCHES, s, conv);
    }


    @Test
    public void testZ3() {


        LOGGER.debug("Test Z3");
        SmtTranslator sa = OutputFormat.Z3STR2.getTranslator();
        try {
            sa.setConstraintNetworkBuilder(cn);
        } catch (NotSupportedException e) {
            assert(true);
        }
        /**String out = null;
        try {
            out = sa.translate();
        } catch (NotSupportedException e) {
            e.printStackTrace();
        }**/

        //LOGGER.debug(out);
    }



    @Test
    public void testCVC4() {

        LOGGER.debug("Test CVC4");
        SmtTranslator sa = OutputFormat.CVC4.getTranslator();
        try {
            sa.setConstraintNetworkBuilder(cn);
        } catch (NotSupportedException e) {
            e.printStackTrace();
        }
        String out = null;
        try {
            out = sa.translate();
        } catch (NotSupportedException | ParseTreeProcessorException e) {
            Assertions.assertFalse(true);
        }

        //LOGGER.debug(out);
    }


    @Test
    public void testCVC4Translator1() {

        try {
            ConstraintNetworkBuilder tm = new ConstraintNetworkBuilder();

            Node x = new Operand("x", DefaultNodeKind.STRVAR);
            Node or = new Operand(".*' +[Oo][Rr] +'", DefaultNodeKind.STRREXP);
            Node v1 = new Operand("sv1", DefaultNodeKind.STRVAR);
            Node orv1 = tm.addOperation(DefaultNodeKind.CONCAT, or, v1);
            Node eq = new Operand("'.*=.*'", DefaultNodeKind.STRREXP);
            Node v2 = new Operand("sv2", DefaultNodeKind.STRVAR);
            Node orv1comp = tm.addOperation(DefaultNodeKind.CONCAT, eq, v2);
            Node orv1compv2 = tm.addOperation(DefaultNodeKind.CONCAT, orv1, orv1comp);

            try {
                tm.addConstraint(DefaultNodeKind.STR_NEQUALS, v1, v2);
            } catch (InconsistencyException e) {
                Assertions.assertFalse(true);
            }
            try {
                tm.addConstraint(DefaultNodeKind.MATCHES, x, orv1compv2);
            } catch (InconsistencyException e) {
                Assertions.assertFalse(true);
            }

            //LOGGER.debug(tm.toDot());

            SmtTranslator sa = OutputFormat.CVC4.getTranslator();
            try {
                sa.setConstraintNetworkBuilder(tm);
            } catch (NotSupportedException e) {
                assert (false);
            }
            String out = "";
            try {
                out = sa.translate();
            } catch (NotSupportedException | ParseTreeProcessorException e) {
                Assertions.assertFalse(true);
            }
        } catch (InconsistencyException e) {
            Assertions.assertFalse(true);
        }

        //LOGGER.debug(out);
    }

    @Test
    public void testCVC4Translator2() {

        try {
            ConstraintNetworkBuilder tm2 = new ConstraintNetworkBuilder();

            Node x = new Operand("x", DefaultNodeKind.STRVAR);
            String sor = ".*' +[Oo][Rr] +'";
            Node or = new Operand(sor, DefaultNodeKind.STRREXP);

            Node v1 = new Operand("sv7", DefaultNodeKind.NUMVAR);

            Node toStrV1 = tm2.addOperation(DefaultNodeKind.TOSTR, v1);

            Node orv1 = tm2.addOperation(DefaultNodeKind.CONCAT, or, toStrV1);

            Node eq = new Operand(" +\\>= +", DefaultNodeKind.STRREXP);

            Node orv1comp = tm2.addOperation(DefaultNodeKind.CONCAT, orv1, eq);

            Node v2 = new Operand("sv8", DefaultNodeKind.NUMVAR);

            Node toStrV2 = tm2.addOperation(DefaultNodeKind.TOSTR, v2);

            Node orv1compv2 = tm2.addOperation(DefaultNodeKind.CONCAT, orv1comp, toStrV2);

            String scomment = "(\\<!\\-\\-|#)";
            Node comment = new Operand(scomment, DefaultNodeKind.STRREXP);

            tm2.addOperation(DefaultNodeKind.CONCAT, orv1compv2, comment);

            tm2.addConstraint(DefaultNodeKind.GREATEREQ, v1, v2);

            tm2.setStartNode(orv1compv2);
            tm2.addConstraint(DefaultNodeKind.MATCHES, x, orv1compv2);

            SmtTranslator sa = OutputFormat.CVC4.getTranslator();
            try {
                sa.setConstraintNetworkBuilder(tm2);
            } catch (NotSupportedException e) {
                assert (false);
            }
            String out = "";
            try {
                out = sa.translate();
            } catch (NotSupportedException | ParseTreeProcessorException e) {
                Assertions.assertFalse(true);
            }
        } catch(InconsistencyException e) {
            Assertions.assertFalse(true);
        }


        //LOGGER.debug(out);
    }

    @Test
    public void testCVC4Escape() {
        String s = "SELECT \\* FROM salaries WHERE userid = ";

        String s2 = CVC4Escape.escapeSpecialCharacters(s);

        LOGGER.debug(s2);

    }

    @Test
    public void testSmtEscape() {
        String s = "\"SELECT \\* FROM salaries WHERE userid = \"";

        String s2 = SmtEscape.trimQuotes(s);

        LOGGER.debug(s2);

    }


    private static String script = "\\< *[Ss][Cc][Rr][Ii][Pp][Tt] *\\>" +
            "[a-zA-Z0-9\\(\\);]+\\</ *[Ss][Cc][Rr][Ii][Pp][Tt] \\>";

    private static String img = "\\< *[Ii][Mm][Gg] [Ss][Rr][Cc]=[Jj][Aa][Vv][Aa][Ss][Cc]" +
            "[Rr][Ii][Pp][Tt]:[a-zA-Z0-9\\(\\);]+ *\\>";

    private static String xss = "(" + script + "|" + img + ")";



}


