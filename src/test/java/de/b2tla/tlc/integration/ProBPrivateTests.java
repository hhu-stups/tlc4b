package de.b2tla.tlc.integration;

import static org.junit.Assert.*;
import static de.b2tla.tlc.TLCOutput.TLCResult.*;

import java.io.File;
import java.util.ArrayList;

import org.junit.Test;
import org.junit.runner.RunWith;

import de.b2tla.tlc.TLCOutput.TLCResult;
import de.b2tla.util.*;
import de.b2tla.util.PolySuite.Config;
import de.b2tla.util.PolySuite.Configuration;

import de.b2tla.B2TLA;
import de.b2tla.B2TLAGlobals;

@RunWith(PolySuite.class)
public class ProBPrivateTests extends AbstractParseMachineTest {

	private final File machine;
	private final TLCResult error;
	
	public ProBPrivateTests(File machine, TLCResult result) {
		this.machine = machine;
		this.error = result;
	}
	
	@Test
	public void testRunTLC() throws Exception {
		String[] a = new String[] { machine.getPath() };
		B2TLAGlobals.setDeleteOnExit(true);
		assertEquals(error, B2TLA.test(a));
	}

	@Config
	public static Configuration getConfig() {
		final ArrayList<TestPair> list = new ArrayList<TestPair>();
		list.add(new TestPair(InvariantViolation, "../probprivate/public_examples/TLC/InvariantViolation"));
		list.add(new TestPair(Deadlock, "../probprivate/public_examples/TLC/Deadlock"));
		list.add(new TestPair(Goal, "../probprivate/public_examples/TLC/GOAL"));
		list.add(new TestPair(NoError, "../probprivate/public_examples/TLC/NoError"));
		list.add(new TestPair(AssertionError, "../probprivate/public_examples/TLC/AssertionError"));
		return getConfiguration(list);
	}


}

