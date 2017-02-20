package nl.tudelft.jpacman.board;
public class Driver{
	Board board;
	public Driver(){
		Square x0y0= new BasicSquare();
		Square x0y1= new BasicSquare();
		Square x1y0= new BasicSquare();
		Square x1y1= new BasicSquare();
		Square x0y2= new BasicSquare();
		Square x1y2= new BasicSquare();
		
		Square[][] grid= new Square[2][3];
		grid[0][0] = x0y0;
		grid[0][1] = x0y1;
		grid[1][0] = x1y0;
		grid[1][1] = x1y1;
		grid[0][2] = x0y2;
		grid[1][2] = x1y2;
		this.board= new Board(grid);
	}
	public Board getBoader(){
		return this.board;
	}
	public static void main(String[] args){
		Driver x= new Driver();
		x.getBoader().withinBorders(2, 2);
	}
}