/*
   Software Reliability Course
   Masters Course on CSE
   Ciencias.ULisboa
   Fall 2022
   
   TicTacToe Board, assignement 2, exercise 4

   Instructor: Antonia Lopes
   Student: TO COMPLETE
*/

/**
 * The pieces that we can place in the board
 * Notice that using a datatype here is simpler than using 
 * integer with complex invariants
*/
datatype Piece = X | O

/**
 * The possible states of a cell of the board.
*/
datatype Cell = Empty | filled(piece:Piece)

method CellToString(c: Cell) returns (s: string)
{
  if c == Empty
  {
    s := " ";
  } 
  else {
    if c.piece == X {
      s := "X";
    }
    else 
    {
      s:= "O";
    }
  }
}
 
/**
 * This class defines a type whose objects represent
 * the state of a cell board with a given dimension. 
 * The cells of the board can be empty or filled with a piece
 */
class Board {

  // dimension of the board
  const DIM := 3;
  
  // number of board cells
  /* private */const CELLS := DIM * DIM;

  // game board
  /* private */var board : array<Cell>;

  // class invariant
  predicate Valid()
  reads this;
  {
    this.board.Length == CELLS 
    
  }

  // Aux function to translate (row,col) to array position
  /* private */
  function method Position(row: nat, col: nat): nat
  requires 1 <= row <= 3 && 1 <= col <= 3;
  {
    (row - 1) * DIM + (col - 1)
  }

  // The constructor
  constructor Init()
    ensures fresh(board)
    ensures this.board.Length == CELLS
    ensures forall i :: 0 <= i < CELLS ==> this.board[i] == Empty
  {
    board := new Cell[CELLS];
    new;
    forall (i | 0 <= i < CELLS ) {
      board[i] := Empty;       
    }
  }

  // Whether the position of the board is filled with a piece
  predicate method IsFilled(row: nat, col: nat)
  requires this.Valid();
  requires 1 <= row <= this.DIM && 1 <= col <= this.DIM; 
  requires Position(row,col) < this.board.Length;
  reads this.board;
  reads this;
  {
      board[Position(row,col)] != Empty 
  }

  // Whether the board is full
  predicate method IsFull()
  requires this.Valid();
  reads this.board;
  reads this;
  ensures IsFull() <==> forall row, col:: 1 <= row <= DIM && 1 <= col <= DIM ==> IsFilled(row, col);
  ensures !IsFull() <==> exists row, col:: 1 <= row <= DIM && 1 <= col <= DIM && !IsFilled(row, col);
  {
    forall row, col:: 1 <= row <= DIM && 1 <= col <= DIM ==> IsFilled(row, col) 
  }


  // Whether the position of the board is filled with a piece
  function method GetPiece(row: nat, col: nat): Piece
  requires this.Valid();
  requires 1 <= row <= this.DIM && 1 <= col <= this.DIM; 
  requires Position(row,col) < this.board.Length;
  requires IsFilled(row,col)
  reads this.board;
  reads this;
  //ensures this.board[Position(row,col)].piece == X || board[Position(row,col)].piece == O;
  {
    board[Position(row,col)].piece
  }

  method Fill(row: nat, col: nat, piece: Piece)
  requires this.Valid();
  requires this.board.Length > 0;
  requires 1 <= row <= 3 && 1 <= col <= 3; 
  ensures IsFilled(row, col) && GetPiece(row, col) == piece;  
   ensures forall r, c :: 1 <= r <= this.DIM && 1 <= c <= this.DIM && Position(r,c) != Position(row,col) 
                    ==> IsFilled(r,c) == old(IsFilled(r,c))
  modifies this.board;
  {
    board[Position(row,col)] := filled(piece);
  }

  method BoardToString() returns (s: string)
  requires this.Valid();
  {
    var i:= 0;
    while (i < CELLS ) {
      var aux := CellToString(board[i]);
      s := s + aux;
      i := i+1;
      if (i % DIM == 0){
        s := s + "\n";
      }
    }
  }

}

method Main () 
{
  
  var board := new Board.Init();     
  assert (!board.IsFilled(1,1));     
   
  var aux : int ;
  aux := board.Position(2,2);
  assert aux == 4 ;
     
  board.Fill(2,2,X);               
  assert board.GetPiece(2,2) == X;

  assert (!board.IsFull());     
     
  aux := board.Position(2,1);
  assert aux == 3 ;     
     
  board.Fill(2,1,O);
  assert board.GetPiece(2,1) == O; 

  board.Fill(1,3,X);
  board.Fill(3,1,O);
  assert (!board.IsFull());  

  var auxS : string;
  auxS := board.BoardToString();
  print "---\n"+auxS+"---\n";
  
}