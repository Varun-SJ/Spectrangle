package test;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import model.Color;
import model.RotatableTile;
import model.TilesBag;

class TestTilesBag {
	
	private TilesBag bag;

	@BeforeEach
	void setUp() throws Exception {
		bag = new TilesBag();
	}

	@Test
	void testTilesBag() {
		assertEquals(36, bag.getBagSize());
	}

	@Test
	void testAddTile() {
		bag.addTile(new RotatableTile(Color.B, Color.R, Color.P, 2));
		
		//Not allowed in the game, but only used for testing the function
		assertEquals(37, bag.getBagSize()); 
		
		bag.addTile(new RotatableTile(Color.R, Color.G, Color.R, 2));
		assertEquals(38, bag.getBagSize());
		
	}

	@Test
	void testIsEmpty() {
		while (!bag.isEmpty()) {
			bag.takeRandomTile();
		}
		
		assertEquals(0, bag.getBagSize());
		assertTrue(bag.isEmpty());
	}

	@Test
	void testTakeRandomTile() {
		bag.takeRandomTile();
		bag.takeRandomTile();
		bag.takeRandomTile();
		
		assertEquals(33, bag.getBagSize());
	}

	@Test
	void testFillStartingBag() {
		while (!bag.isEmpty()) {
			bag.takeRandomTile();
		}
		
		assertEquals(0, bag.getBagSize());
		bag.fillStartingBag();
		assertEquals(36, bag.getBagSize());
	}

}
