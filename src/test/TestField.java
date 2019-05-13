package test;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import model.Color;
import model.Field;
import model.RotatableTile;
import model.Board;

class TestField {

	@BeforeEach
	void setUp() throws Exception {
	}

	@Test
	void testField() {
		Field field1 = new Field(1, 1);
		Field field4 = new Field(3, 4);
		
		assertEquals(1, field1.getIndex());
		assertEquals(3, field4.getIndex());
		
		assertEquals(1, field1.getMultiplier());
		assertEquals(4, field4.getMultiplier());
	}

	@Test
	void testPutTile() {
		Field field = new Field(0, 1);
		RotatableTile tile = new RotatableTile(Color.P, Color.R, Color.B, 5);
		
		assertFalse(field.hasTile());
		assertNull(field.getTile());
		
		field.putTile(tile);
		
		assertTrue(field.hasTile());
		assertEquals(tile, field.getTile());
	}

	@Test
	void testHasTile() {
		Board board = new Board();
		RotatableTile tile = new RotatableTile(Color.B, Color.B, Color.B, 6);
		
		board.setField(35, tile);
		assertTrue(board.hasTile(35), "BBB6");
	}

	@Test
	void testIsBonus() {
		Field field1 = new Field(4, 1);
		Field field3 = new Field(7, 3);
		
		assertFalse(field1.isBonus());
		assertTrue(field3.isBonus());
	}

	@Test
	void testIsUpsideDown() {
		Field fieldIndex2 = new Field(2, 3);
		Field fieldIndex22 = new Field(22, 1);
		
		assertTrue(fieldIndex2.isUpsideDown());
		assertFalse(fieldIndex22.isUpsideDown());
	}
	
}
