
#include <assert.h>
#include <stdio.h>
#include <stdbool.h>

int nondet_int();
void __CPROVER_printf(const char *format, ...);

void simulate_seu(int *x) {
	static count  = 0;
	if(count == 0) {
		*x = 10;
		count++;
	}
}

// Global variables to store values of x that satisfy and violate the property
int satisfy_x_p = -1;
int violate_x_p = -1;
int satisfy_x_p_prime = -1;
int violate_x_p_prime = -1;

int x_in_p = -1;
int x_in_p_prime = -1;

int main() {

int output, x, y;
CPROVER_assume(x >= 0 && x <= 20); // Example assumption for positive x
CPROVER_assume (y >= 0 && y <= 20); // Example assumption for positive y

output = p(x, y); // OriginalProgram
int x_output = P_prime_x(x, y); // p'(x): Instrumented program, x is being the variable under invest.
int y_output = p_prime_y(x, y); // p' (y): Instrumented program, y is being the variable under investi

int phi = output <= 10;
int phi_prime_x = x_output <= 10;
int phi_prime_y = y_output <= 10;

// Logic to capture when the property is satisfied or violated in Psha.s@CORP
if (phi && satisfy_x_p == -1) {
	satisfy_x_p = x; // Capture & when the property is satisfied in P
}
if (!phi && violate_x_p == -1) {
    violate_x_p = x; // Capture when the property is violated in P(X)
}

// Logic to capture when the property is satisfied or violated in P'(x)
if (phi_prime_x && satisfy_x_p_prime == -1) {
    satisfy_x_p_prime = x_in_p_prime; // Capture when the property is satisfied in P'(X)
}
if (!phi_prime_x && violate_x_p_prime == -1){
    violate_x_p_prime = x_in_p_prime; // Capture when the property is violated in P'(X)
}

// Check and print results
if (satisfy_x_p != -1 && violate_x_p_prime != -1) {
	__CPROVER_printf(" value in P(X) satisfying the property: %d\n", satisfy_x_p);
	__CPROVER_printf("value in P(X) violating the property: %d\n", violate_x_p_prime);
	//assert(0); // Force CBMC to stop and display output
}

if (violate_x_p != -1 && satisfy_x_p_prime != -1) {
	__CPROVER_printf("x value in P(x) violating the property: %d\n", violate_x_p);
	__CPROVER_printf("x value in P'(x) satisfying the property: %d\n", satisfy_x_p_prime);
       // assert(0); // Force CBMC to stop and display output
}

//Check CRV for x: We need to find and Ix such that (phi XOR phi_prime_x) is true
CPROVER_assert(!(phi^ phi_prime_x), "Check CRV for x => SUCCESS = Not a CRV and FAILURE = Its a CRV ?");

//Check CRV for y: We need to find and Ix such that (phi XOR phi_prime_y) is true
CPROVER_assert(!(phi^ phi_prime_y), "Check CRV for y => SUCCESS = Not a CRV and FAILURE = Its a CRV ?");

return 0; 

}

// Function to generate a nondeterministic integer within the range [1, 32]
int nondet_int_range_1_32() {
	int value = nondet_int() % 32 + 1;
	__CPROVER_assume (value >= 1 && value <= 32); // Example assumption for positive x
	return value;
}


int simulate_seu(int value, int bit_pos)
{
	int mask = 1 << bit_pos;
	__CPROVER_assume (mask >= 1 && mask <= 32);
	return (value ^ mask);
}

int p(int x, int y) {
	int output = 4;
	bool alarm = false;
	int count = 0;
	while (count < 7) {
		if (x > 10) {
			if (y == 1) {
				output = 2;
			} else {
			    output = 1;
		    }
		} else {
			output = output + 1;
		    alarm = true;
		}
		count++;
	}
	return output;
}


int p_prime_x(int x, int y) {
	int output = 4, seu_x;
	bool alarm = false;
	int count = 0;
	
	x = nondet_int();
	// Assuming some initial conditions if needed (optional)
	__CPROVER_assume (x >= 0 && x <= 20); // Example assumption for positive x
	
	int bit_pos = nondet_int_range_1_32();
	__CPROVER_assume (bit_pos >= 1 && bit_pos <= 32);
	__CPROVER_assert (bit_pos >= 1 && bit_pos <= 32, "Bit flip position is in the range [1..32]"); // This assert should never fail

	while (count < 7) {
		_CPROVER_assume (x >= 0 && x <= 20); // Example assumption for positive x
		seu_x = simulate_seu(x, bit_pos); // before every use of x, introduce SEU
		//__CPROVER_printf("Values ox x = %d and seu_x = %d", x, seu_x);
		if (seu_x > 10) {
			if (y == 1) {
			    output = 2;
			} else {
			    output = 1;
			}
		} else {
			output = output + 1;
			alarm = true;
		}
		count++;
	}
	return output;
}

int p_prime_y(int x, int y) {

	int output = 4, seu_y;
	bool alarm = false;
	int count = 0;
	
	y = nondet_int();
	// Assuming some initial conditions if needed (optional)
	__CPROVER_assume (y >= 0 && y <= 20); // Example assumption for positive y
	
	int bit_pos = nondet_int_range_1_32();
	__CPROVER_assume (bit_pos >= 1 && bit_pos <= 32);
	__CPROVER_assert (bit_pos >= 1 && bit_pos <= 32, "Bit flip position is in the range [1..32]"); // This assert should never fail
	while (count < 7) {
		if (x > 10) {
		    __CPROVER_assume (y >= 0 && y <= 20); // Example assumption for positive y
		    seu_y  = simulate_seu (y, bit_pos); // before every use of y, introduce SEU
			if (seu_y== 1) {
				output = 2;
			} else {
				output = 1;
			}
		} else {
		output = output + 1;
		alarm = true;
		}
		count++;
	}
	return output;
}
