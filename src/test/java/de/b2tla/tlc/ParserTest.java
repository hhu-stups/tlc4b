package de.b2tla.tlc;

import static de.b2tla.util.TestUtil.*;

import java.util.Hashtable;

import org.junit.Test;

import de.b2tla.btypes.BType;
import de.b2tla.btypes.BoolType;
import de.b2tla.btypes.IntegerType;
import de.b2tla.btypes.PairType;

public class ParserTest {

	@Test
	public void testTupleOneElement() throws Exception {
		String tla = " x = <<1>>";
		String b = "x = [1]";
		compareExpr(b, tla);
	}

	@Test
	public void testEmptyTuple() throws Exception {
		String tla = " x = <<>>";
		String b = "x = []";
		compareExpr(b, tla);
	}

	@Test
	public void testTupleTwoElements() throws Exception {
		String tla = " x = <<1,1>>";
		String b = "x = [1,1]";
		compareExpr(b, tla);
	}

	@Test
	public void testModelvalue() throws Exception {
		String tla = " x = model";
		String b = "x = model";
		compareExpr(b, tla);
	}

	@Test
	public void testModelvalue2() throws Exception {
		String tla = " x = {a,b}";
		String b = "x = {a,b}";
		compareExpr(b, tla);
	}
	
	@Test
	public void testFunction() throws Exception {
		String tla = "x = (3 :> TRUE @@ 4 :> TRUE)";
		String b = "x = { (3,TRUE), (4,TRUE)}";
		compareExpr(b, tla);
	}

	@Test
	public void testSetOneElement() throws Exception {
		String tla = "x = {3}";
		String b = "x = {3}";
		compareExpr(b, tla);
	}

	@Test
	public void testEmptySet() throws Exception {
		String tla = "x = {}";
		String b = "x = {}";
		compareExpr(b, tla);
	}

	@Test
	public void testSetOfTuple() throws Exception {
		String tla = "x = {<<1,2,3>>}";
		String b = "x = {[1,2,3]}";
		compareExpr(b, tla);
	}

	@Test
	public void testPairVsSequence() throws Exception {
		String tla = "x = <<1,TRUE>>";
		String b = "x = (1,TRUE)";
		Hashtable<String, BType> types = new Hashtable<String, BType>();
		types.put("x",
				new PairType(IntegerType.getInstance(), BoolType.getInstance()));
		compareExpr(b, tla, types);
	}

	@Test
	public void testPedicates() throws Exception {
		String tla = "x = {<<1,2,3>>}\n /\\ y = <<1>>";
		String b = "x = {[1,2,3]} & y = [1]";
		compareExpr(b, tla);
	}
	
}
