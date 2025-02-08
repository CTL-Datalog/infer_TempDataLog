/*

/*@ AF(z=1) @*/

/*
GUARANTEE (z == 1)

suggested parameters:
- partition abstract domain = boxes [default]
- function abstract domain = affine [default]
- backward widening delay = 2 [default]
*/

void main() {
	int x = 0, y = 0, z = 0;

	int t1 = __VERIFIER_nondet_int();
	int t2 = __VERIFIER_nondet_int();
	int t3 = __VERIFIER_nondet_int();
	int t4 = __VERIFIER_nondet_int();
	int t5 = __VERIFIER_nondet_int();
	
	// x = 1;
	// await (y > 0);
	// z = 1;
	//
	// await (x > 0);
	// y = 1;
	if (x > 0) {
		// x = 1;
		// await (y > 0);
		// z = 1;
		//
		// y = 1;
		if (t1) {
			x = 1;
			// await (y > 0);
			// z = 1;
			//
			// y = 1;
			if (y > 0) {
				// z = 1;
				//
				// y = 1;
				if (t2) {
					z = 1;
					y = 1;
				} else {
					y = 1;
					z = 1;
				}
			} else {
				y = 1;
				// await (y > 0);
				// z = 1;
				while (y <= 0);
				z = 1;
			}
		} else {
			y = 1;
			// x = 1;
			// await (y > 0);
			// z = 1;
			x = 1;
			while (y <= 0);
			z = 1;
		}
	} else {
		x = 1;
		// await (y > 0);
		// z = 1;
		//
		// await (x > 0);
		// y = 1;
		if (x > 0 && y > 0) {
			if (t3) {
				z = 1;
				// await (x > 0);
				// y = 1;
				while (x <= 0);
				y = 1;
			} else {
				y = 1;
				// await (y > 0);
				// z = 1;
				while (y <= 0);
				z = 1;
			}
		} else if (x > 0) {
			// await (y > 0);
			// z = 1;
			//
			// y = 1;
			if (y > 0) {
				// z = 1;
				//
				// y = 1;
				if (t4) {
					z = 1;
					y = 1;
				} else {
					y = 1;
					z = 1;
				}
			} else {
				y = 1;
				// await (y > 0);
				// z = 1;
				while (y <= 0);
				z = 1;
			}
		} else if (y > 0) {
			// z = 1;
			//
			// await (x > 0);
			// y = 1;
			if (x > 0) {
				// z = 1;
				//
				// y = 1;
				if (t5) {
					z = 1;
					y = 1;
				} else {
					y = 1;
					z = 1;
				}
			} else {
				z = 1;
				// await (x > 0);
				// y = 1;
				while (x <= 0);
				y = 1;
			}
		} else {
			//
		}
	}

}