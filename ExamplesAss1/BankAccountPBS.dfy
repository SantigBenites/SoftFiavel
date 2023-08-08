/**
 * Reliable Software
 * Masters Course on CSE
 * Department of Informatics
 * Faculty of Sciences
 * University of Lisbon
 * November 7, 2022
 * Vasco T. Vasconcelos
 * Antonia Lopes
 *
 * A property-based specification of a bank account.
 *
 * The observer is the method Balance().
 * The contracts of all methods are based on this method.
 * Balance() is both a method and a function. A method so that it may be
 * used in code; a function so that it may be used in contracts.
 *
 * The invariant is captured in predicate Valid().
 * Constructors establish the invariant.
 * All methods require the invariant and reestablish it in the end.
 * Pragma {:autocontracts} does this for you.
 */
class {:autocontracts} BankAccount {
    var balance: int;
    function method Balance(): int
    {
        balance
    }
    predicate Valid ()
    {
        balance >= 0    // the invariant
    }
    constructor ()
        ensures Balance() == 0
    {
        balance := 0;
    }
    constructor Init (initBalance: nat)
        ensures Balance() == initBalance
    {
        balance := initBalance;
    }
    method Withdraw (amount: nat)
        modifies this
        requires Balance() >= amount
        ensures Balance() == old(Balance()) - amount
    {
        balance := balance - amount;
    }
    method Deposit (amount: nat)
        modifies this
        ensures Balance() == old(Balance()) + amount
    {
        balance := balance + amount;
    }
    method TransferToDifferentAccount (other: BankAccount, amount: nat)
        modifies this, other
        requires other.Valid()
        ensures other.Valid()
        requires this.Balance() >= amount
        requires this != other
        ensures this.Balance() == old(this.Balance()) - amount
        ensures other.Balance() == old(other.Balance()) + amount
    {
        this.Withdraw(amount);
        other.Deposit(amount);
    }
    method TransferUnacceptable (other: BankAccount, amount: nat)
        modifies this, other
        requires other.Valid()
        ensures other.Valid()
        requires this.Balance() >= amount
        ensures this != other ==>
            this.Balance() == old(this.Balance()) - amount &&
            other.Balance() == old(other.Balance()) + amount
    {
        if this != other {
            this.Withdraw(amount);
            other.Deposit(amount);
        }
        else {
            this.balance := 0;
        }
    }
    method Transfer (other: BankAccount, amount: nat)
        modifies this, other
        requires other.Valid()
        ensures  this.Valid() && other.Valid()
        requires this.Balance() >= amount
        ensures this != other ==>
            this.Balance() == old(this.Balance()) - amount &&
            other.Balance() == old(other.Balance()) + amount
        ensures this == other ==>
            this.Balance() == old(this.Balance())
    {
        this.Withdraw(amount);
        other.Deposit(amount);
    }
    method Test ()  // Did you get our contracts right?
    {
        var a := new BankAccount.Init(5);
        assert a.Balance() == 5;
        a.Withdraw(3);
        a.Deposit(7);
        assert a.Balance() == 9;
        a.Transfer(a, 5);
        assert a.Balance() == 9;
        var b := new BankAccount.Init(0);
        a.Transfer(b, 3);
        assert a.Balance() == 6;
        assert b.Balance() == 3;
    }
}
method Main()   // Some people enjoy running programs (I'd rather prove them correct)
{
    var a := new BankAccount.Init(5);
    print a.Balance(); print '\n';
    a.Withdraw(3);
    print a.Balance(); print '\n';
    a.Deposit(7);
    print a.Balance(); print '\n';
    a.Transfer(a, 8);
    print a.Balance(); print '\n';
    var b := new BankAccount();
    a.Transfer(b, 3);
    print a.Balance(); print '\n';
    print b.Balance(); print '\n';
}
