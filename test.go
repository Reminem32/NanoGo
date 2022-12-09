package main
import "fmt"

type T struct { a,b int }
// type T struct { a,e int } OK
// type T2 struct { a,a int } OK

func foo(t  T) { t.a = t.a + 1; t.b = t.b + 1;  }
func bar(t *T) { t.a = t.a + 1; t.b = t.b + 1;  }


//func crash(a,a int) {
//	return
//} OK

// type rec struct {a rec} OK
type rec1 struct {a *rec2}
type rec2 struct {a rec1}

func main() {
	var t T
	t.a = 1
	t.b = 2
	fmt.Print(t.a, t.b, "\n");
	foo(t)
	fmt.Print(t.a, t.b, "\n");
	bar(&t)
	fmt.Print(t.a, t.b, "\n");
	fmt.Print("5" + 37);
}
