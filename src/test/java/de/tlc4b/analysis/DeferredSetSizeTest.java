package de.tlc4b.analysis;

import de.tlc4b.util.TestUtil;

import org.junit.Test;

public class DeferredSetSizeTest {
	@Test
	public void testDeferredSetStandard() throws Exception {
		String machine = "MACHINE test\n"
				+ "SETS S \n"
				+ "END";
		String expectedModule = "---- MODULE test ----\n"
				+ "CONSTANTS S\n"
				+ "====";
		String expectedConfig = "CONSTANTS\nS = {S1,S2,S3}\n"; 
		TestUtil.compareModuleAndConfig(expectedModule, expectedConfig, machine);
	}
	
	@Test
	public void testDeferredSet() throws Exception {
		String machine = "MACHINE test\n"
				+ "SETS S \n"
				+ "PROPERTIES card(S) = 4"
				+ "END";
		String expectedModule = "---- MODULE test ----\n"
				+ "EXTENDS FiniteSets\n"
				+ "CONSTANTS S\n"
				+ "ASSUME Cardinality(S) = 4\n"
				+ "====";
		String expectedConfig = "CONSTANTS\nS = {S1,S2,S3,S4}\n"; 
		TestUtil.compareModuleAndConfig(expectedModule, expectedConfig, machine);
	}
	
	@Test
	public void testDeferredSet2() throws Exception {
		String machine = "MACHINE test\n"
				+ "SETS S \n"
				+ "PROPERTIES 4 = card(S)"
				+ "END";
		String expectedModule = "---- MODULE test ----\n"
				+ "EXTENDS FiniteSets\n"
				+ "CONSTANTS S\n"
				+ "ASSUME 4 = Cardinality(S)\n"
				+ "====";
		String expectedConfig = "CONSTANTS\nS = {S1,S2,S3,S4}\n"; 
		TestUtil.compareModuleAndConfig(expectedModule, expectedConfig, machine);
	}
}
