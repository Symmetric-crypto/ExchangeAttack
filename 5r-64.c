/*
* rijndael-alg-ref.c   v2.2   March 2002
* Reference ANSI C code
* authors: Paulo Barreto
*          Vincent Rijmen
*
* This code is placed in the public domain.
*/

/*
The code is modifed to imeplement the small-scale variant of AES (AES-64)
*/

/*
 5 rounds distinguisher for AES
 
 For 5-round of AES-64, the probability of having right pairs are 2^{-12.19-14}=2^{-26.19}
 if we choose |m1|=|m2|=2^7, we can contruct 2^{13}.2^{13}=2^{26} pairs.
 
 author: Navid Ghaedi Bardeh
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#define Round 5
#define setA 128    //|m1|
#define setB 128    //|m2|
#define Ntest 10

typedef unsigned char word8;
word8 S4[16] = {12,5,6,11,9,0,10,13,3,14,15,8,4,7,1,2};
word8 S4i[16] = {5, 14, 15, 8, 12, 1, 2, 13, 11, 4, 6, 3, 0, 7, 9, 10};
word8 mul2[16]={0,2,4,6,8,10,12,14,3,1,7,5,11,9,15,13};
word8 rcon4[10] = {0x01,0x02, 0x04, 0x08, 0x3, 0x6, 0xc, 0xb, 0x5, 0xa};

word8 pl[setA][setB][16];
word8 ci[setA][setB][16];

static word8 shifts[3][4][2] = {
	{{0, 0},
		{1, 3},
		{2, 2},
		{3, 1}},
	
	{{0, 0},
		{1, 5},
		{2, 4},
		{3, 3}},
	
	{{0, 0},
		{1, 7},
		{3, 5},
		{4, 4}}
};

void AddRoundKey(word8 a[4][4], word8 rk[4][4]) {
	int i, j;
	for(i = 0; i < 4; i++)
		for(j = 0; j < 4; j++)
			a[i][j] ^= rk[i][j];
}

void ShiftRows(word8 a[4][4], word8 d) {
	/* Row 0 remains unchanged
	 * The other three rows are shifted a variable amount
	 */
	word8 tmp[4];
	int i, j;
	
	for(i = 1; i < 4; i++) {
		for(j = 0; j < 4; j++)
			tmp[j] = a[i][(j + shifts[0][i][d]) % 4];
		for(j = 0; j < 4; j++)
			a[i][j] = tmp[j];
	}
}

void Substitution(word8 a[4][4], word8 box[16]) {
	/* Replace every byte of the input by the byte at that place
	 * in the nonlinear S-box.
	 * This routine implements SubBytes and InvSubBytes
	 */
	int i, j;
	for(i = 0; i < 4; i++)
		for(j = 0; j < 4; j++) a[i][j] = box[a[i][j]] ;
}

void MixColumns(word8 a[4][4]) {
	/* Mix the four bytes of every column in a linear way
	 */
	word8 b[4][4];
	int i, j;
	for(j = 0; j < 4; j++)
		for(i = 0; i < 4; i++)
			b[i][j] = mul2[a[i][j]]
			^ mul2[a[(i + 1) % 4][j]] ^ a[(i + 1) % 4][j]
			^ a[(i + 2) % 4][j]
			^ a[(i + 3) % 4][j];
	for(i = 0; i < 4; i++)
		for(j = 0; j < 4; j++) a[i][j] = b[i][j];
}

void InvMixColumns(word8 a[4][4]) {
	/* Mix the four bytes of every column in a linear way
	 * This is the opposite operation of Mixcolumns
	 */
	word8 b[4][4];
	int i, j;
	
	for(j = 0; j < 4; j++)
		for(i = 0; i < 4; i++)
			b[i][j] = mul2[(mul2[(mul2[a[i][j]])])] ^ mul2[(mul2[a[i][j]])] ^ mul2[a[i][j]]
			^ mul2[(mul2[(mul2[a[(i + 1) % 4][j]])])] ^ mul2[a[(i + 1) % 4][j]] ^ a[(i + 1) % 4][j]
			^ mul2[(mul2[(mul2[a[(i + 2) % 4][j]])])] ^ mul2[(mul2[a[(i + 2) % 4][j]])]  ^ a[(i + 2) % 4][j]
			^ mul2[(mul2[(mul2[a[(i + 3) % 4][j]])])] ^ a[(i + 3) % 4][j];
	

	for(i = 0; i < 4; i++)
		for(j = 0; j < 4; j++) a[i][j] = b[i][j];
}

int rijndaelKeySched (word8 k[4][4],  word8 W[11][4][4]) {
	/* Calculate the necessary round keys
	 */
	int i, j, t, rconpointer = 0;
	word8 tk[4][4];
	
	for(j = 0; j < 4; j++)
		for(i = 0; i < 4; i++)
			tk[i][j] = k[i][j];
	t = 0;
	/* copy values into round key array */
	for(j = 0; (j < 4) && (t < 44); j++, t++)
		for(i = 0; i < 4; i++) W[t / 4][i][t % 4] = tk[i][j];
	
	while (t < 44) {
		/* while not enough round key material calculated */
		/* calculate new values */
		for(i = 0; i < 4; i++)
			tk[i][0] ^= S4[tk[(i+1)%4][3]];
		
		tk[0][0] ^= rcon4[rconpointer++];
		
		
		for(j = 1; j < 4; j++)
			for(i = 0; i < 4; i++) tk[i][j] ^= tk[i][j-1];
		
		/* copy values into round key array */
		for(j = 0; (j < 4) && (t < 44); j++, t++)
			for(i = 0; i < 4; i++) W[t / 4][i][t % 4] = tk[i][j];
	}
	return 0;
}

/* Everything above here is code related to AES made by Barreto and Rijmen */

int randomInRange(int min, int max){
	int range = max - min + 1;
	int a, b, c, d;
	a = rand() % range;
	b = rand() % range;
	c = rand() % range;
	d = (a*b) % range;
	d = (d+c) % range;
	return (min + d);
}

word8 randomByte(){
	return (word8) randomInRange(0, 15);
}

void PrintXOR(const word8 block1[4][4],const word8 block2[4][4]){
	int i, j;
	for(i = 0; i < 4; i++) {
		for(j = 0; j < 4; j++) {
			printf("%X ", block1[i][j]^block2[i][j]);
		} printf("\n");
	}
	printf("\n");
}

void Print(const word8 block1[4][4]){
	int i, j;
	for(i = 0; i < 4; i++) {
		for(j = 0; j < 4; j++)
			printf("%X ", block1[i][j]);
		printf("\n");
	}
	printf("\n");
}


/*
 Equal to 5 rounds AES encryption minus last MC,SR
 */
int Enc5(word8 a[4][4],word8 rk[11][4][4]){
	
	int r;
	
	AddRoundKey(a,rk[0]);
	
	for(r = 0; r < Round-1; r++) {
		Substitution(a,S4);
		ShiftRows(a,0);
		MixColumns(a);
		AddRoundKey(a,rk[r+1]);
	}
	Substitution(a,S4);
	//    ShiftRows(a,0);
	//    MixColumns(a);
	AddRoundKey(a,rk[Round]);
	
	return 0;
}

///////////////////////////////////////////////////////////////////////////////////////////////
unsigned int CheckColumns(word8 p[4][4]){
	int i,j,z,counter;
	counter = 0;
	for(i=0; i<4 ; i++){
		z = 0;
		for(j=0; j<4 ; j++){
			if (p[j][i] != 0)
				z = 1;
		}
		if (z == 0){
			counter^=(1<<i);
		}
	}
	return (counter);
}
///////////////////////////////////////////////////////////////////
unsigned int AEScase(word8 key[][4]){
	unsigned int i,j,k,r,counter,counter1,counter2,counter3,counter4,counter5,coset,ind,flag,z,flag1;
	unsigned int n1,n2,n3,n4;
	word8 rp[4][4],rp1[4][4],rp2[4][4],rp3[4][4];
	unsigned int m,m1,m2,m3;
	word8 sa[setA][4],sb[setB][4];
	word8 temp[4][4],temp1[4][4],temp2[4][4],temp3[4][4],sumc[4][4],sump[4][4],test[4][4],test1[4][4],test2[4][4],test3[4][4];
	word8 rk[11][4][4];
	
	rijndaelKeySched(key,rk);
	counter=0;
	for(i=0;i<4;i++)
		for(j=0;j<4;j++)
			pl[0][0][4*i+j] =randomByte();
	for(i=0;i<setA;i++)
		for(j=0;j<setB;j++)
			for(k=0;k<16;k++)
				pl[i][j][k]=pl[0][0][k];
	
	for(i=0;i<4;i++)
		sa[0][i] =randomByte();
	for(i=0;i<4;i++)
		sb[0][i] =randomByte();
	
	//choose random values for set A
	for(i=1; i<setA ;i++){
		do{
			flag1 = 0;
			temp[0][0] = randomByte();
			temp[1][0] = randomByte();
			temp[2][0] = randomByte();
			temp[3][0] = randomByte();
			for(k=0; k<i; k++){
				flag = 0;
				for(j=0;j<4;j++){
					if(sa[k][j] == temp[j][0])
						flag++;
					}
				if(flag==4){
					flag1 = 1;
					break;
				}
			}
			if(flag1 == 0){
				for(j=0;j<4;j++)
					sa[i][j]= temp[j][0];
			}
		}while(flag1 == 1);
	}
	//choose random values for set B
	for(i=1; i<setB ;i++){
		do{
			flag1 = 0;
			temp[0][0] = randomByte();
			temp[1][0] = randomByte();
			temp[2][0] = randomByte();
			temp[3][0] = randomByte();
			for(k=0; k<i; k++){
				flag = 0;
				for(j=0;j<4;j++){
					if(sb[k][j] == temp[j][0])
						flag++;
				}
				if(flag==4){
					flag1 = 1;
					break;
				}
			}
			if(flag1 == 0){
				for(j=0;j<4;j++)
					sb[i][j]= temp[j][0];
			}
		}while(flag1 == 1);
	}
	// contruct  m1.m2  plaintexts
	for(m=0;m<setA;m++){
		for(m1=0;m1<setB;m1++){
			
			pl[m][m1][0] = sa[m][0];
			pl[m][m1][5] = sa[m][1];
			pl[m][m1][10] = sa[m][2];
			pl[m][m1][15] =sa[m][3];
			
			pl[m][m1][1] = sb[m1][0];
			pl[m][m1][6] = sb[m1][1];
			pl[m][m1][11] = sb[m1][2];
			pl[m][m1][12] = sb[m1][3];
			
			for(i=0; i<4 ;i++)
				for(j=0; j<4 ;j++)
					temp[i][j]=pl[m][m1][4*i+j];
			
			Enc5(temp,rk);
			
			for(i=0; i<4 ;i++)
				for(j=0; j<4 ;j++)
					ci[m][m1][4*i+j]= temp[i][j];
		}
	}
	
	counter=0;
	counter1=0;
	// contruct 2^{26} ciphertext pairs
	for(m=0;m<setA;m++){
		for(m1=m+1;m1<setA;m1++){
			for(m2=0;m2<setB;m2++){
				for(m3=m2+1;m3<setB;m3++){
			
					// check for first collision
					for(i=0; i<4 ;i++)
						for(j=0; j<4 ;j++)
							test[i][j] = ci[m][m2][4*i+j] ^ ci[m1][m3][4*i+j];
					
					coset=CheckColumns(test);
					if (coset){
						counter++;
						// check for second collision, just swap the first index between the pair (equals to swap the first diagonal between their plaintexts)
						for(i=0; i<4 ;i++)
							for(j=0; j<4 ;j++)
								test1[i][j] = ci[m1][m2][4*i+j] ^ ci[m][m3][4*i+j];
						
						if (coset==CheckColumns(test1)){
							counter1++;
								for(i=0; i<4 ;i++)
									for(j=0; j<4 ;j++)
										test2[i][j]=ci[m][m2][4*i+j] ;
								for(i=0; i<4 ;i++)
									for(j=0; j<4 ;j++)
										test3[i][j]=ci[m1][m3][4*i+j] ;
								printf("right pairs \n");
								printf("C1:\n");
								Print(test2);
								printf("C2:\n");
								Print(test3);
								printf("C1+C2:\n");
								PrintXOR(test2,test3);
								
								for(i=0; i<4 ;i++)
									for(j=0; j<4 ;j++)
										test2[i][j]=ci[m1][m2][4*i+j] ;
								for(i=0; i<4 ;i++)
									for(j=0; j<4 ;j++)
										test3[i][j]=ci[m][m3][4*i+j] ;
								
								printf("C3:\n");
								Print(test2);
								printf("C4:\n");
								Print(test3);
								printf("C3+C4:\n");
								PrintXOR(test2,test3);
								
								for(i=0; i<4 ;i++)
									for(j=0; j<4 ;j++)
										test3[i][j]=pl[m][m2][4*i+j] ;
								printf("P1:\n");
								Print(test3);
								for(i=0; i<4 ;i++)
									for(j=0; j<4 ;j++)
										test3[i][j]=pl[m1][m3][4*i+j] ;
								printf("P2:\n");
								Print(test3);
								for(i=0; i<4 ;i++)
									for(j=0; j<4 ;j++)
										test3[i][j]=pl[m1][m2][4*i+j] ;
								printf("P3:\n");
								Print(test3);
								for(i=0; i<4 ;i++)
									for(j=0; j<4 ;j++)
										test3[i][j]=pl[m][m3][4*i+j] ;
								printf("P4:\n");
								Print(test3);
						}
					}
				}
			}
		}
	}
	
	printf("Number of the right pairs for AES: %d \n",counter1);
	
	return (counter1);
}
//////////////////////////////////////////////////////////////////
unsigned int Randomcase(word8 key[][4]){
	unsigned int i,j,k,r,counter,counter1,counter2,counter3,counter4,counter5,coset,ind,flag,z,flag1;
	unsigned int n1,n2,n3,n4;
	word8 rp[4][4],rp1[4][4],rp2[4][4],rp3[4][4];
	unsigned int m,m1,m2,m3;
	word8 sa[setA][4],sb[setB][4];
	word8 temp[4][4],temp1[4][4],temp2[4][4],temp3[4][4],sumc[4][4],sump[4][4],test[4][4],test1[4][4],test2[4][4],test3[4][4];
	word8 rk[11][4][4];
	
	rijndaelKeySched(key,rk);
	counter=0;
	for(i=0;i<4;i++)
		for(j=0;j<4;j++)
			pl[0][0][4*i+j] =randomByte();
	for(i=0;i<setA;i++)
		for(j=0;j<setB;j++)
			for(k=0;k<16;k++)
				pl[i][j][k]=pl[0][0][k];
	
	for(i=0;i<4;i++)
		sa[0][i] =randomByte();
	for(i=0;i<4;i++)
		sb[0][i] =randomByte();
	//choose random values for set A
	for(i=1; i<setA ;i++){
		do{
			flag1 = 0;
			temp[0][0] = randomByte();
			temp[1][0] = randomByte();
			temp[2][0] = randomByte();
			temp[3][0] = randomByte();
			for(k=0; k<i; k++){
				flag = 0;
				for(j=0;j<4;j++){
					if(sa[k][j] == temp[j][0])
						flag++;
				}
				if(flag==4){
					flag1 = 1;
					break;
				}
			}
			if(flag1 == 0){
				for(j=0;j<4;j++)
					sa[i][j]= temp[j][0];
			}
		}while(flag1 == 1);
	}
	//choose random values for set B
	for(i=1; i<setB ;i++){
		do{
			flag1 = 0;
			temp[0][0] = randomByte();
			temp[1][0] = randomByte();
			temp[2][0] = randomByte();
			temp[3][0] = randomByte();
			for(k=0; k<i; k++){
				flag = 0;
				for(j=0;j<4;j++){
					if(sb[k][j] == temp[j][0])
						flag++;
				}
				if(flag==4){
					flag1 = 1;
					break;
				}
			}
			if(flag1 == 0){
				for(j=0;j<4;j++)
					sb[i][j]= temp[j][0];
			}
		}while(flag1 == 1);
	}
	
	for(m=0;m<setA;m++){
		for(m1=0;m1<setB;m1++){
			
			pl[m][m1][0] = sa[m][0];
			pl[m][m1][5] = sa[m][1];
			pl[m][m1][10] = sa[m][2];
			pl[m][m1][15] =sa[m][3];
			
			pl[m][m1][1] = sb[m1][0];
			pl[m][m1][6] = sb[m1][1];
			pl[m][m1][11] = sb[m1][2];
			pl[m][m1][12] = sb[m1][3];
			
			for(i=0; i<4 ;i++)
				for(j=0; j<4 ;j++)
					temp[i][j]=pl[m][m1][4*i+j];
			
			Enc5(temp,rk);
			Enc5(temp,rk);
			
			for(i=0; i<4 ;i++)
				for(j=0; j<4 ;j++)
					ci[m][m1][4*i+j]= temp[i][j];
		}
	}
	
	counter=0;
	counter1=0;
	for(m=0;m<setA;m++){
		for(m1=m+1;m1<setA;m1++){
			for(m2=0;m2<setB;m2++){
				for(m3=m2+1;m3<setB;m3++){
					
					for(i=0; i<4 ;i++)
						for(j=0; j<4 ;j++)
							test[i][j] = ci[m][m2][4*i+j] ^ ci[m1][m3][4*i+j];
					coset=CheckColumns(test);
					if (coset){
						counter++;
						for(i=0; i<4 ;i++)
							for(j=0; j<4 ;j++)
								test1[i][j] = ci[m1][m2][4*i+j] ^ ci[m][m3][4*i+j];
						
						if (coset==CheckColumns(test1)){
							counter1++;
						}
					}
					
				}
			}
		}
	}
	
	printf("Nmuber of the right pairs for Random case: %d \n",counter1);

	return (counter1);
}
///////////////////////////////////
int main() {
	sranddev();
	int i,j,k;
	unsigned counter=0,counter1=0;
	word8 key[4][4];
	
	printf("Round %d \n",Round);
	for( i=0; i< 4; i++)
		for( j=0; j < 4; j++)
			key[i][j] =rand() & 0xf;
	printf("key \n");
	for( i=0; i< 4; i++){
		for( j=0; j < 4; j++){
			printf("%X ",key[i][j]);
		}
		printf("\n");
	}
	printf("\n");

	counter=0;
	counter1=0;
	for( i=0; i< Ntest; i++){
		counter+=AEScase(key);
		counter1+=Randomcase(key);
	}
	printf("\n\n");
	printf("Total number of the right pairs in AES case: %d \n",counter);
	printf("Total number of the right pairs in Random case %d \n",counter1);
	
}




