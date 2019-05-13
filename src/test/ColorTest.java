package test;

import static org.junit.jupiter.api.Assertions.*;
import org.junit.jupiter.api.Test;

import model.Color;

class ColorTest {

	@Test
	void isValidAdjacentToColour() {
		assertFalse(Color.R.isValidAdjacent(Color.G));
		assertFalse(Color.Y.isValidAdjacent(Color.G));
		
		assertTrue(Color.Y.isValidAdjacent(Color.Y));
		assertTrue(Color.G.isValidAdjacent(Color.G));
		
	}
	
	@Test
	void isValidAdjacentToWhite() {
		
		assertTrue(Color.B.isValidAdjacent(Color.W));
		assertTrue(Color.G.isValidAdjacent(Color.W));
		assertTrue(Color.Y.isValidAdjacent(Color.W));
		assertTrue(Color.R.isValidAdjacent(Color.W));
		assertTrue(Color.W.isValidAdjacent(Color.W));
		
	}


}
