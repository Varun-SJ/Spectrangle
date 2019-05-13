package test;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import model.Color;
import model.SimpleTile;

class TestSimpleTile {
	
	SimpleTile tile;

	@BeforeEach
	void setUp() throws Exception {
		tile = new SimpleTile(Color.Y, Color.R, Color.Y, 4);
	}

	@Test
	void testSimpleTile() {
		assertEquals(tile.getRightSide(), Color.Y);
		assertEquals(tile.getOtherSide(), Color.R);
		assertEquals(tile.getLeftSide(), Color.Y);
	}

	@Test
	void testGenerateTileString() {
		boolean isUpsideDown = false;
		System.out.println(tile.generateTileString(isUpsideDown));
		
		isUpsideDown = true; 
		System.out.println(tile.generateTileString(isUpsideDown));
	}

}
