#include <stdio.h>
#include <memory.h>
#include <stdlib.h>
#define BYTE unsigned char  //�w�qByte��8��bits�զX
#define EBC    1
#define CBC    2
#define CTR    3
#define OFB    4
#define CFB    5
#define CFB_8   6 
#define AES_BLOCK_SIZE    16
void printBytes(BYTE b[], int len) {
  int i;
  for (i=0; i<len; i++){
  	if(i%16==0) printf("\n");
    printf("%x  ", b[i]);
  }
  printf("\n");
}

BYTE AES_Sbox[] = 
{ 
  99,124,119,123,242,107,111,197,48,1,103,43,254,215,171,
  118,202,130,201,125,250,89,71,240,173,212,162,175,156,164,114,192,183,253,
  147,38,54,63,247,204,52,165,229,241,113,216,49,21,4,199,35,195,24,150,5,154,
  7,18,128,226,235,39,178,117,9,131,44,26,27,110,90,160,82,59,214,179,41,227,
  47,132,83,209,0,237,32,252,177,91,106,203,190,57,74,76,88,207,208,239,170,
  251,67,77,51,133,69,249,2,127,80,60,159,168,81,163,64,143,146,157,56,245,
  188,182,218,33,16,255,243,210,205,12,19,236,95,151,68,23,196,167,126,61,
  100,93,25,115,96,129,79,220,34,42,144,136,70,238,184,20,222,94,11,219,224,
  50,58,10,73,6,36,92,194,211,172,98,145,149,228,121,231,200,55,109,141,213,
  78,169,108,86,244,234,101,122,174,8,186,120,37,46,28,166,180,198,232,221,
  116,31,75,189,139,138,112,62,181,102,72,3,246,14,97,53,87,185,134,193,29,
  158,225,248,152,17,105,217,142,148,155,30,135,233,206,85,40,223,140,161,
  137,13,191,230,66,104,65,153,45,15,176,84,187,22
};

BYTE AES_ShiftRowTab[] = {0,5,10,15,4,9,14,3,8,13,2,7,12,1,6,11};   //���Nshiftrow�L��C�Ӥ����|�첾�쪺��l�s���}�C
BYTE AES_Sbox_Inv[256];
BYTE AES_ShiftRowTab_Inv[16];
BYTE AES_xtime[256];
FILE *f_encrypt,*f_decrypt,*f,*fkey,*fIV;

void AES_SubBytes(BYTE state[], BYTE sbox[]) {
  int i;
  for(i = 0; i < 16; i++)
    state[i] = sbox[state[i]];      // ��S_Box����������
}

void AES_AddRoundKey(BYTE state[], BYTE rkey[]) {
  int i;
  for(i = 0; i < 16; i++)
    state[i] ^= rkey[i];
}

void AES_ShiftRows(BYTE state[], BYTE shifttab[]) {
  BYTE h[16];
  memcpy(h, state, 16);
  int i;
  for(i = 0; i < 16; i++)
    state[i] = h[shifttab[i]];
}

void AES_MixColumns(BYTE state[]) {
  int i;
  for(i = 0; i < 16; i += 4) {
    BYTE s0 = state[i + 0], s1 = state[i + 1];
    BYTE s2 = state[i + 2], s3 = state[i + 3];
    BYTE h = s0 ^ s1 ^ s2 ^ s3;

    /*�z�L��²MixColumn�x�}(03 02 01 01)*state���x�}�i�H�o�X�U�C���G*/

    state[i + 0] ^= h ^ AES_xtime[s0 ^ s1];
    state[i + 1] ^= h ^ AES_xtime[s1 ^ s2];
    state[i + 2] ^= h ^ AES_xtime[s2 ^ s3];
    state[i + 3] ^= h ^ AES_xtime[s3 ^ s0];
  }
}

void AES_MixColumns_Inv(BYTE state[]) {
  int i;
  for(i = 0; i < 16; i += 4) {
    BYTE s0 = state[i + 0], s1 = state[i + 1];
    BYTE s2 = state[i + 2], s3 = state[i + 3];
    BYTE h = s0 ^ s1 ^ s2 ^ s3;
    BYTE xh = AES_xtime[h];
    BYTE h1 = AES_xtime[AES_xtime[xh ^ s0 ^ s2]] ^ h;
    BYTE h2 = AES_xtime[AES_xtime[xh ^ s1 ^ s3]] ^ h;

    /*�z�L��²InvMixColumn�x�}(0E 0B 0D 09)*state���x�}�i�H�o�X�U�C���G*/

    state[i + 0] ^= h1 ^ AES_xtime[s0 ^ s1];
    state[i + 1] ^= h2 ^ AES_xtime[s1 ^ s2];
    state[i + 2] ^= h1 ^ AES_xtime[s2 ^ s3];
    state[i + 3] ^= h2 ^ AES_xtime[s3 ^ s0];
  }
}
void AES_Init() {
  int i;
  for(i = 0; i < 256; i++)
    AES_Sbox_Inv[AES_Sbox[i]] = i;

  for(i = 0; i < 16; i++)
    AES_ShiftRowTab_Inv[AES_ShiftRowTab[i]] = i;

  /*���Nxtime����X���G�ئ����*/

  for(i = 0; i < 128; i++) {
    AES_xtime[i] = i << 1;
    AES_xtime[128 + i] = (i << 1) ^ 0x1b;
  }
}
int AES_ExpandKey(BYTE key[], int keyLen) {
  int Nk = keyLen, ks, Rcon = 1, i, j; 
  BYTE temp[4], temp2[4];  //�Q��temp,temp2 �Ӱ� Rotword
  switch (Nk) { //ks�����_�j�p�A(Nr+1)*4(word)�A�ڭ̳o�̥�byte�]���|����(Nr+1)*16(byte)
    case 16: ks = 16 * (10 + 1); break;  // AES-128 Nr=10
    case 24: ks = 16 * (12 + 1); break;  // AES-196 Nr=12
    case 32: ks = 16 * (14 + 1); break;  // AES-256 Nr=14
    default:
      printf("AES_ExpandKey: Only key lengths of 16, 24 or 32 bytes allowed!");
  }
  for(i = Nk; i < ks; i += 4) {   // �쥻��key�|�Q�ƻs�b�eNk��A�]���q��Nk��}�l���B��A�@���B���쬰�@��word�A4bytes=1word�A�]���@��i+4
    memcpy(temp, &key[i-4], 4);   // ���N�W�@��word��key�s�btemp��
    if (i % Nk == 0) {            // �㰣�����p�A��w[i] = w[i-Nk] ^ SubWord(RotWord(w[i-4])) ^ Rcon[i/Nk]�A�o�̧ڭ̥��� (SubWord(RotWord(w[i-4])) ^ Rcon[i/Nk])�D�X
      temp2[0] = AES_Sbox[temp[1]] ^ Rcon;  // Rcon�u���Ĥ@��Byte���ȡAtemp2�Ptemp�o���γB�A�]��RotWord���V���첾�@��Byte�A�ҥH�n�D�Xtemp2[0]�����G�ڭ̭n��temp[1]�ӨD�C
      temp2[1] = AES_Sbox[temp[2]];
      temp2[2] = AES_Sbox[temp[3]];
      temp2[3] = AES_Sbox[temp[0]];
      memcpy(temp, temp2, 4);
      if ((Rcon <<= 1) >= 256)     //���챡�p�A�n%(x8+x4+x2+x+1)�A����xor 11B
        Rcon ^= 0x11b;
    }
    else if ((Nk > 24) && (i % Nk == 16)) {  //AES-256�~�|�o�ͪ����p�A��w[i] = w[i-Nk] ^ SubWord(w[i-4])�C�o�̧ڭ̰�SubWord(w[i-4])�Y�i
      temp2[0] = AES_Sbox[temp[0]];
      temp2[1] = AES_Sbox[temp[1]];
      temp2[2] = AES_Sbox[temp[2]];
      temp2[3] = AES_Sbox[temp[3]];
      memcpy(temp, temp2, 4);
    }
    for(j = 0; j < 4; j++)
      key[i + j] = key[i + j - Nk] ^ temp[j]; //�W���S���쪺w[i-Nk]�b�o�䰵�A�]���o�O�������p���������C
}
  return ks;
}

void AES_Encrypt(BYTE block[], BYTE key[], int keyLen) {
  int l = keyLen, i;
  AES_AddRoundKey(block, &key[0]);
  for(i = 16; i < l - 16; i += 16) {
    AES_SubBytes(block, AES_Sbox);
    AES_ShiftRows(block, AES_ShiftRowTab);
    AES_MixColumns(block);
    AES_AddRoundKey(block, &key[i]);
  }
  AES_SubBytes(block, AES_Sbox);
  AES_ShiftRows(block, AES_ShiftRowTab);
  AES_AddRoundKey(block, &key[i]);
}

void AES_Decrypt(BYTE block[], BYTE key[], int keyLen) {
  int l = keyLen, i;
  AES_AddRoundKey(block, &key[l - 16]);
  AES_ShiftRows(block, AES_ShiftRowTab_Inv);
  AES_SubBytes(block, AES_Sbox_Inv);
  for(i = l - 32; i >= 16; i -= 16) {
    AES_AddRoundKey(block, &key[i]);
    AES_MixColumns_Inv(block);
    AES_ShiftRows(block, AES_ShiftRowTab_Inv);
    AES_SubBytes(block, AES_Sbox_Inv);
  }
  AES_AddRoundKey(block, &key[0]);
}

int padding(int dataLen){
  int i = 0;
  while((dataLen+i)%16!=0) // ��X����128bits���Ŷ���padding
    i++;
  return i;
}

void AES_EBC_Encrypt(BYTE key[], int expandkeyLen, BYTE data[], int total){
  int i;
  for (i = 0; i < total; i += AES_BLOCK_SIZE)
  	AES_Encrypt(&data[i], key, expandkeyLen);  //�@�Ӱ϶��@�Ӱ϶��[�K
}

void AES_EBC_Decrypt(BYTE key[], int expandkeyLen, BYTE data[], int total){
  int i;
  for(i = 0; i < total; i += AES_BLOCK_SIZE)
    AES_Decrypt(&data[i], key, expandkeyLen);   //�@�Ӱ϶��@�Ӱ϶��ѱK
}

void AES_CBC_Encrypt(BYTE key[], int expandkeyLen, BYTE data[], int total, BYTE IV[]){
  int i,j;
  BYTE tempIV[AES_BLOCK_SIZE];
  memcpy(tempIV, IV, AES_BLOCK_SIZE);
  
  for (i = 0; i < total; i += AES_BLOCK_SIZE){
    for(j = i; j< i+16; j++)
      data[j] ^= tempIV[j % AES_BLOCK_SIZE];   // ���� XOR IV�A���[�K
  	AES_Encrypt(&data[i], key, expandkeyLen);
  	memcpy(tempIV, &data[i], AES_BLOCK_SIZE);   // �[�K�᪺�K�� = �U�@����IV
  }
}

void AES_CBC_Decrypt(BYTE key[], int expandkeyLen, BYTE data[], int total, BYTE IV[]){
  int i,j;
  BYTE tempIV[total];
  memcpy(tempIV, IV, AES_BLOCK_SIZE);
  memcpy(&tempIV[AES_BLOCK_SIZE], data, total-AES_BLOCK_SIZE);
  
  for (i = 0; i < total; i += AES_BLOCK_SIZE){
  	AES_Decrypt(&data[i], key, expandkeyLen);  // �����ѱK
    for(j = i; j < i+16; j++)
      data[j] ^= tempIV[j];  
  }
}

void AES_CTR(BYTE key[], int expandkeyLen, BYTE data[], int dataLen, BYTE IV[]){  //�[�ѱK�@�Ҥ@�� 
  int i,j;
  BYTE tempIV[AES_BLOCK_SIZE];
  memcpy(tempIV, IV, AES_BLOCK_SIZE); // ��tempIV���NIV���B��A�O��IV���|�Q�󴫡C 
  
  for(i=0; i < dataLen; i += AES_BLOCK_SIZE){
  	AES_Encrypt(tempIV, key, expandkeyLen);
  	for(j = 0; j < AES_BLOCK_SIZE; j++){
  	  if((i + j) >= dataLen) break;
  	  data[i + j] ^= tempIV[j];
    }
    memcpy(tempIV, IV, AES_BLOCK_SIZE);
	for (j = AES_BLOCK_SIZE-1; j >= 0; j--)   // ��������+1 
	  if (++tempIV[j]) break; //�i�쪬�p 
  }
}

void AES_OFB(BYTE key[], int expandkeyLen, BYTE data[], int dataLen, BYTE IV[]) { // �[�ѱK�@�Ҥ@�� 
  int i;
  BYTE tempIV[AES_BLOCK_SIZE];        //���F�����N��lIV 
  memcpy(tempIV, IV, AES_BLOCK_SIZE);
  
  for(i = 0; i < dataLen; i++){
  	if(i % AES_BLOCK_SIZE == 0)
  	  AES_Encrypt(tempIV, key, expandkeyLen);        //�[�K�᪺IV����U�@����IV 
    data[i] ^= tempIV [i % AES_BLOCK_SIZE];
  }
}

void AES_CFB_Encrypt(BYTE key[], int expandkeyLen, BYTE data[], int dataLen, BYTE IV[]){ 
  int i;
  BYTE tempIV[AES_BLOCK_SIZE];
  memcpy(tempIV, IV, AES_BLOCK_SIZE);
  for(i = 0; i < dataLen; i++){
  	if(i % AES_BLOCK_SIZE == 0)   // �C�@�����@�}�l 
  	  AES_Encrypt(tempIV, key, expandkeyLen);
    data[i] ^= tempIV [i % AES_BLOCK_SIZE];
    if((i+1) % AES_BLOCK_SIZE == 0)  // �C�@�������� 
      memcpy(tempIV, &data[i-15], AES_BLOCK_SIZE);     // XOR�᪺�K��|����U�@�������� 
  }
}

void AES_CFB_Decrypt(BYTE key[], int expandkeyLen, BYTE data[], int dataLen, BYTE IV[]){ 
  int i;
  BYTE tempIV[AES_BLOCK_SIZE], nextIV[AES_BLOCK_SIZE];  //nextIV �s�U�@���ѱK�Ϊ�IV 
  memcpy(tempIV, IV, AES_BLOCK_SIZE);    
  for(i = 0; i < dataLen; i++){
  	if(i % AES_BLOCK_SIZE == 0){
  	  AES_Encrypt(tempIV, key, expandkeyLen);
  	  memcpy(nextIV, &data[i], AES_BLOCK_SIZE);  // �C����IV����W�@�����K�� 
    }
    data[i] ^= tempIV [i % AES_BLOCK_SIZE];
    if((i+1) % AES_BLOCK_SIZE == 0)
      memcpy(tempIV, nextIV, AES_BLOCK_SIZE);      
  }
}

void AES_CFB_8_Encrypt(BYTE key[], int expandkeyLen, BYTE data[], int dataLen, BYTE IV[]){ 
  int i;
  BYTE tempIV[AES_BLOCK_SIZE];
  memcpy(tempIV, IV, AES_BLOCK_SIZE);
  for(i = 0; i < dataLen; i++){
  	if(i % 8 == 0)   // �C�@�����@�}�l 
  	  AES_Encrypt(tempIV, key, expandkeyLen);
    data[i] ^= tempIV [i % 8];
    if((i+1) % 8 == 0)  {// �C�@��������  
      memcpy(tempIV, &tempIV[8], 8);          // IV���e��8bits 
      memcpy(&tempIV[8], &data[i-7], 8);     // IV��8�ӳQ8bits�K����N 
    } 
  }
}

void AES_CFB_8_Decrypt(BYTE key[], int expandkeyLen, BYTE data[], int dataLen, BYTE IV[]){ 
  int i;
  BYTE tempIV[AES_BLOCK_SIZE], nextIV[AES_BLOCK_SIZE];
  memcpy(tempIV, IV, AES_BLOCK_SIZE);
  for(i = 0; i < dataLen; i++){
  	if(i % 8 == 0){   // �C�@�����@�}�l 
  	  AES_Encrypt(tempIV, key, expandkeyLen);
  	  memcpy(nextIV, &tempIV[8], 8);
  	  memcpy(&nextIV[8], &data[i], 8);
    }
    data[i] ^= tempIV [i % 8];
    if((i+1) % 8 == 0)  // �C�@��������  
      memcpy(tempIV, nextIV, AES_BLOCK_SIZE);
  }
}

void Load(int *keyLen, int *dataLen){
  char subname[10];
  char filename[30];
  char filekey[30] = "key.txt";
  char fileIV[30] = "IV.txt";
  char encrypt[30] = "encrypt.";
  char decrypt[30] = "decrypt.";
  
  printf("�п�J�ɮצW��: ");
  scanf("%s",&filename);
  
  f = fopen(filename,"rb");
  fkey = fopen(filekey,"rb");
  fIV = fopen(fileIV,"rb");
  
  fseek(f, 0, SEEK_END);
  *dataLen = ftell(f);
  fseek(f, 0, SEEK_SET);
  fseek(fkey, 0, SEEK_END);
  *keyLen = ftell(fkey);
  fseek(fkey, 0, SEEK_SET);
  
  int i;
  for(i=0;i<strlen(filename);i++)
  	if (filename[i]=='.'){  // �P�_���ɦW�A�H���D�ڭ̸ӫإߤ����ɮ�  
      memcpy(subname, &filename[i+1], strlen(filename)-i);
      break;
    }
  strcat(encrypt,subname); 
  strcat(decrypt,subname);
  f_encrypt = fopen(encrypt,"wb");
  f_decrypt = fopen(decrypt,"wb");
}

int main() {
  AES_Init();
  int mode, pad, dataLen, keyLen;
  BYTE *data, *key, IV[AES_BLOCK_SIZE];
  Load(&keyLen, &dataLen);
  printf("��ܥ[�K�Ҧ�:\n 1.ECB 2.CBC 3.CTR 4.OFB 5.CFB 6.CFB_8\n");
  scanf("%d", &mode);
  
  switch(keyLen){
  	case 16: key = malloc(16*(10+1)*sizeof(BYTE)); break;
  	case 24: key = malloc(16*(12+1)*sizeof(BYTE)); break;
  	case 32: key = malloc(16*(14+1)*sizeof(BYTE)); break;
  	default:
      printf("���_������128,196,256 bits\n");
      return 0;
  }
  
  if(mode==CBC||mode==EBC){     // CBC&EBC�Ҧ��ݭnpadding 
	pad = padding(dataLen);
	data = malloc((dataLen + pad) * sizeof(BYTE));
	memset(data, 0, (dataLen + pad)); // �Ndata�����]��0
  }
  else
    data = malloc(dataLen * sizeof(BYTE));
  // �}�lŪ�� 
  if(mode!=EBC) 
    fread(IV,AES_BLOCK_SIZE,1,fIV);
  fread(data,dataLen,1,f);
  fread(key,keyLen,1,fkey);
  fclose(fIV);
  fclose(f);
  fclose(fkey);
  
  int expandKeyLen = AES_ExpandKey(key, keyLen);

  switch(mode){
    case EBC:
      AES_EBC_Encrypt(key, expandKeyLen, data, (dataLen + pad));
      printf("�K��: ");printBytes(data, (dataLen + pad));
      fwrite(data, (dataLen+pad), 1, f_encrypt);
      AES_EBC_Decrypt(key, expandKeyLen, data, (dataLen + pad));
      printf("����: ");printBytes(data, dataLen);
      fwrite(data, dataLen, 1, f_decrypt);
      break;
    case CBC:
      AES_CBC_Encrypt(key, expandKeyLen, data, (dataLen + pad), IV);
      printf("�K��: ");printBytes(data, (dataLen+pad));
      fwrite(data, (dataLen+pad), 1, f_encrypt);
      AES_CBC_Decrypt(key, expandKeyLen, data, (dataLen + pad), IV);
      printf("����: ");printBytes(data, dataLen);
      fwrite(data, dataLen, 1, f_decrypt);
      break;
    case CTR:
      AES_CTR(key, expandKeyLen, data, dataLen, IV);
      printf("�K��: ");printBytes(data, dataLen);
      fwrite(data, dataLen, 1, f_encrypt);
      AES_CTR(key, expandKeyLen, data, dataLen, IV);
      printf("����: ");printBytes(data, dataLen);
      fwrite(data, dataLen, 1, f_decrypt);
      break;
    case OFB:
      AES_OFB(key, expandKeyLen, data, dataLen, IV);
      printf("�K��: ");printBytes(data, dataLen);
      fwrite(data, dataLen, 1, f_encrypt);
      AES_OFB(key, expandKeyLen, data, dataLen, IV);
      printf("����: ");printBytes(data, dataLen);
      fwrite(data, dataLen, 1, f_decrypt);
      break;
    case CFB:
      AES_CFB_Encrypt(key, expandKeyLen, data, dataLen, IV);
      printf("�K��: ");printBytes(data, dataLen);
      fwrite(data, dataLen, 1, f_encrypt);
      AES_CFB_Decrypt(key, expandKeyLen, data, dataLen, IV);
      printf("����: ");printBytes(data, dataLen);
      fwrite(data, dataLen, 1, f_decrypt);
      break;
    case CFB_8:
      AES_CFB_8_Encrypt(key, expandKeyLen, data, dataLen, IV);
      printf("�K��: ");printBytes(data, dataLen);
      fwrite(data, dataLen, 1, f_encrypt);
      AES_CFB_8_Decrypt(key, expandKeyLen, data, dataLen, IV);
      printf("����: ");printBytes(data, dataLen);
      fwrite(data, dataLen, 1, f_decrypt);
      break;
  }
  fclose(f_encrypt);
  fclose(f_decrypt);
}


