#ifndef SSACODESTRUCT_HPP
#define SSACODESTRUCT_HPP
#include <vector>
#include "frontEndInput.hpp"
#include "functionBlock.hpp"
using namespace std;

static unordered_map<string,symb*> s_varList;
static unordered_map<string,symb*> s_funcList;
static unordered_map<string,symb*> s_labelList;

struct SsaTac;
struct SsaSymb;
struct UseSsaTac;
struct SsaTac
{
    int type;		
    int blockId;	
	int priority;	
    SsaSymb* first;	
    SsaSymb* second;
    SsaSymb* third;
	vector<SsaSymb*> functionSymb;
	vector<UseSsaTac*> functionSymb2Tac;
    UseSsaTac* firstPoint;
    UseSsaTac* secondPoint;
    UseSsaTac* thirdPoint;
    SsaTac* prev;
    SsaTac* next;
    SsaTac()
    {
        type = blockId = -1;
        prev = next = NULL;
        first = second = third = NULL;
        firstPoint = secondPoint = thirdPoint = NULL;
		functionSymb.clear();
		functionSymb2Tac.clear();
    }
};

struct UseSsaTac
{
    SsaTac* code;
    UseSsaTac* prev;
    UseSsaTac* next;
    UseSsaTac()
    {
        code = NULL;
        prev = next = NULL;
    }
};

struct SsaSymb
{
    int type;
    int value;
    int label;
    char* name;
    int useTimes;
    SsaTac* defPoint;  
    UseSsaTac* useList;
    SsaSymb()
    {
        type = -1;
        value = -1;
        name = new char[50];
        name[0] = '\0';
        useTimes = 0;
        defPoint = NULL;
        useList = new UseSsaTac();
    }
};

void deleteUseSsaTac(UseSsaTac* point);
void printOneSsaTac(SsaTac* node);
void printSsaTacs(SsaTac* tacHead);
SsaTac* createSsaTacFromTac(tac* code);
SsaSymb* createSsaSymbFromSymb(symb* var);
SsaSymb* createSsaSymbFromSsaSymb(SsaSymb* var);
void setDefPointForSsaSymb(SsaTac* node,SsaSymb* var);
void addTacToUseListForSsaSymb(SsaTac* &node,SsaSymb* &var,UseSsaTac* &useTacPoint);
SsaTac* transTacIntoSsaTac(tac* headNode);

tac* createTacFromSsaTac(SsaTac* code);
symb* createSymbFromSsaSymb(SsaSymb* var);
symb* lookForVar(SsaSymb* var);
symb* lookForFunc(SsaSymb* var);
symb* lookForLabel(SsaSymb* var);
void clearFunc(void);
void clearLabel(void);
void clearVar(void);



SsaTac* createSsaTacFromTac(tac* code)
{
    SsaTac* newCode = new SsaTac();
    newCode->type = code->op;
    if(code->a != NULL)
        newCode->first = createSsaSymbFromSymb(code->a);
    if(code->b != NULL)
        newCode->second = createSsaSymbFromSymb(code->b);
    if(code->c != NULL)
        newCode->third = createSsaSymbFromSymb(code->c);  
    return newCode;
}

SsaSymb* createSsaSymbFromSymb(symb* var);
    SsaSymb* newSymb = new SsaSymb();
    newSymb->type = var->type;
    switch(var->type)
    {
        case SYM_VAR:
        case SYM_ARRAY:
        case SYM_FUNC:
        case SYM_LABEL:
            strcpy(newSymb->name,var->name);
            break;
        case SYM_TEXT:
            strcpy(newSymb->name,var->name);
            newSymb->label = var->label;
            break;
        case SYM_INT:
            newSymb->value = var->value;
            break;
    }
    return newSymb;
}

SsaSymb* createSsaSymbFromSsaSymb(SsaSymb* var)
{
    SsaSymb* newSymb = new SsaSymb();
    newSymb->type = var->type;
    switch(var->type)
    {
        case SYM_VAR:
        case SYM_ARRAY:
        case SYM_FUNC:
        case SYM_LABEL:
            strcpy(newSymb->name,var->name);
            break;
        case SYM_TEXT:
            strcpy(newSymb->name,var->name);
            newSymb->label = var->label;
            break;
        case SYM_INT:
            newSymb->value = var->value;
            break;
    }
    return newSymb;
}

void setDefPointForSsaSymb(SsaTac* node,SsaSymb* var)
{
	if(var == NULL)return;
	var->defPoint = node;
}


const char* tsOfSsa(SsaSymb* s, char* str)
{
	if (s == NULL)
	{
		return "(nullptr)";
	}

	switch (s->type)
	{
	case SYM_FUNC:
	case SYM_VAR:
	case SYM_ARRAY:
	case SYM_LABEL:
		return s->name; 

	case SYM_TEXT:
		sprintf(str, "S%d", s->label);
		return str;

	case SYM_INT:
		sprintf(str, "%d", s->value);
		return str;

	default:
		printf("unknown TAC arg type: %d\n", s->name);
		return NULL;
	}
}

void printOneSsaTac(SsaTac* node)
{
	char sa[100]; 
	char sb[100];
	char sc[100];
    switch (node->type)
    {
	case TAC_UNDEF:
		printf("undef");
		break;
	case TAC_INSERT:
		printf("%s = insert(",tsOfSsa(node->first, sa));
		for(int i = 0;i < node->functionSymb.size()-1;i++)
			printf("%s,",tsOfSsa(node->functionSymb[i], sa));
		if(node->functionSymb.size() >= 1)
			printf("%s",tsOfSsa(node->functionSymb[node->functionSymb.size()-1], sa));
		printf(")");
		break;
	case TAC_ADD:
		printf("%s = %s + %s", tsOfSsa(node->first, sa), tsOfSsa(node->second, sb), tsOfSsa(node->third, sc));
		break;

	case TAC_SUB:
		printf("%s = %s - %s", tsOfSsa(node->first, sa), tsOfSsa(node->second, sb), tsOfSsa(node->third, sc));
		break;

	case TAC_MUL:
		printf("%s = %s * %s", tsOfSsa(node->first, sa), tsOfSsa(node->second, sb), tsOfSsa(node->third, sc));
		break;

	case TAC_DIV:
		printf("%s = %s / %s", tsOfSsa(node->first, sa), tsOfSsa(node->second, sb), tsOfSsa(node->third, sc));
		break;

	case TAC_EQ:
		printf("%s = (%s == %s)", tsOfSsa(node->first, sa), tsOfSsa(node->second, sb), tsOfSsa(node->third, sc));
		break;
	case TAC_MOD:
		printf("%s = (%s %% %s)", tsOfSsa(node->first, sa), tsOfSsa(node->second, sb), tsOfSsa(node->third, sc));
		break;
	case TAC_NE:
		printf("%s = (%s != %s)", tsOfSsa(node->first, sa), tsOfSsa(node->second, sb), tsOfSsa(node->third, sc));
		break;

	case TAC_LT:
		printf("%s = (%s < %s)", tsOfSsa(node->first, sa), tsOfSsa(node->second, sb), tsOfSsa(node->third, sc));
		break;

	case TAC_LE:
		printf("%s = (%s <= %s)", tsOfSsa(node->first, sa), tsOfSsa(node->second, sb), tsOfSsa(node->third, sc));
		break;

	case TAC_GT:
		printf("%s = (%s > %s)", tsOfSsa(node->first, sa), tsOfSsa(node->second, sb), tsOfSsa(node->third, sc));
		break;

	case TAC_GE:
		printf("%s = (%s >= %s)", tsOfSsa(node->first, sa), tsOfSsa(node->second, sb), tsOfSsa(node->third, sc));
		break;
	case TAC_OR:
		printf("%s = (%s || %s)", tsOfSsa(node->first, sa), tsOfSsa(node->second, sb), tsOfSsa(node->third, sc));
		break;
	case TAC_AND:
		printf("%s = (%s && %s)", tsOfSsa(node->first, sa), tsOfSsa(node->second, sb), tsOfSsa(node->third, sc));
		break;
	case TAC_NEG:
		printf("%s = - %s", tsOfSsa(node->first, sa), tsOfSsa(node->second, sb));
		break;
	case TAC_POSI:
		printf("%s = + %s", tsOfSsa(node->first, sa), tsOfSsa(node->second, sb));
		break;
	case TAC_NOT:
		printf("%s = ! %s", tsOfSsa(node->first, sa), tsOfSsa(node->second, sb));
		break;
	case TAC_COPY:
		printf("%s = %s", tsOfSsa(node->first, sa), tsOfSsa(node->second, sb));
		break;

	case TAC_GOTO:
		printf("goto %s", tsOfSsa(node->first,sa));
		break;

	case TAC_IFZ:
		printf("ifz %s goto %s", tsOfSsa(node->first,sa), tsOfSsa(node->second, sb));
		break;
	case TAC_IFEQ:
		printf("if %s == %s goto %s", tsOfSsa(node->first,sa), 
		tsOfSsa(node->third, sb),tsOfSsa(node->second, sc));
		break;
	case TAC_IFNE:
		printf("if %s != %s goto %s", tsOfSsa(node->first,sa),
		tsOfSsa(node->third, sb),tsOfSsa(node->second, sc));
		break;
	case TAC_IFLT:
		printf("if %s < %s goto %s", tsOfSsa(node->first,sa),
		tsOfSsa(node->third, sb),tsOfSsa(node->second, sc));
		break;
	case TAC_IFLE:
		printf("if %s <= %s goto %s", tsOfSsa(node->first,sa),
		tsOfSsa(node->third, sb),tsOfSsa(node->second, sc));
		break;
	case TAC_IFGT:
		printf("if %s > %s goto %s", tsOfSsa(node->first,sa),
		tsOfSsa(node->third, sb),tsOfSsa(node->second, sc));
		break;
	case TAC_IFGE:
		printf("if %s >= %s goto %s", tsOfSsa(node->first,sa),
		tsOfSsa(node->third, sb),tsOfSsa(node->second, sc));
		break;
	case TAC_ACTUAL:
		printf("actual %s", tsOfSsa(node->first, sa));
		break;

	case TAC_FORMAL:
		printf("formal %s", tsOfSsa(node->first, sa));
		break;

	case TAC_CALL:
		if(node->first != NULL)
			printf("%s = call %s", tsOfSsa(node->first, sa), tsOfSsa(node->second,sb));
		else printf("call %s", tsOfSsa(node->second,sb));
		break;

	case TAC_RETURN:
		if(node->first != NULL)
			printf("return %s", tsOfSsa(node->first, sa));
		else printf("return");
		break;

	case TAC_LABEL:
		printf("label %s", tsOfSsa(node->first,sa));
		break;

	case TAC_VAR:
		printf("var %s", tsOfSsa(node->first, sa));
		break;

	case TAC_BEGINFUNC:
		printf("begin");
		break;

	case TAC_ENDFUNC:
		printf("end");
		break;
	case TAC_ARR_L:
		printf("%s[%s]=%s", tsOfSsa(node->first, sa), tsOfSsa(node->second, sb), tsOfSsa(node->third, sc));
		break;
	case TAC_ARR_R:
		printf("%s=%s[%s]", tsOfSsa(node->first, sa), tsOfSsa(node->second, sb), tsOfSsa(node->third, sc));
		break;
	case TAC_ARR:
		printf("var %s[%s]", tsOfSsa(node->first,sa), tsOfSsa(node->second,sb));
		break;
	case TAC_LEA:
		printf("%s=&%s[%s]", tsOfSsa(node->first, sa), tsOfSsa(node->second, sb), tsOfSsa(node->third, sc));
		break;
	case TAC_STR:
		printf("S%d=\"%s\"", tsOfSsa(node->first,sb), tsOfSsa(node->first,sc));
		break;
	case TAC_FUNC:
		printf("\nFunc %s", tsOfSsa(node->first,sa));
		break;
		case TAC_ZERO:
		printf("%s[%s...%s]=0", tsOfSsa(node->first, sa), tsOfSsa(node->second, sb), tsOfSsa(node->third, sc));
		break;
	default:
		printf("unknown TAC opcode");
		break;
	}
}

void printSsaTacs(SsaTac* tacHead)
{
    SsaTac* node = tacHead;
    while(node != NULL)
    {
        printOneSsaTac(node);
        node = node->next;
        printf("\n");
    }
}


void addTacToUseListForSsaSymb(SsaTac* &node,SsaSymb* &var,UseSsaTac* &useTacPoint)
{
	
	UseSsaTac* useListTail = var->useList;
	while(useListTail->next != NULL)
	{
		if(useListTail->next->code == node)
		{
			useTacPoint = NULL;
			return;
		}
		useListTail = useListTail->next;
	}
	UseSsaTac* addNode = new UseSsaTac();
	addNode->code = node;
	useListTail->next = addNode;
	addNode->prev = useListTail;
	var->useTimes++;
	useTacPoint = addNode;
}

void deleteUseSsaTac(UseSsaTac* point)
{
	if(point == NULL)return;
	UseSsaTac* pointNext = point->next;
	UseSsaTac* pointPrev = point->prev;
	if(pointPrev != NULL)
		pointPrev->next = point->next;
	if(pointNext != NULL)
		pointNext->prev = point->prev;
	delete point;
}

SsaTac* transTacIntoSsaTac(tac* headNode)
{
	if(headNode == NULL)return NULL;
	SsaTac* sHeadNode = createSsaTacFromTac(headNode);
	SsaTac* sTailNode = sHeadNode;
	while(headNode->next != NULL)
	{
		SsaTac* sHeadNodeNext = createSsaTacFromTac(headNode->next);
		sHeadNodeNext->prev = sTailNode;
		sTailNode->next = sHeadNodeNext;
		sTailNode = sHeadNodeNext;
		headNode = headNode->next;
	}
	return sHeadNode;
}

tac* createTacFromSsaTac(SsaTac* code)
{
    tac* newCode = new tac();
    newCode->op = code->type;
    if(code->first != NULL)
        newCode->a = createSymbFromSsaSymb(code->first);
    if(code->second != NULL)
        newCode->b = createSymbFromSsaSymb(code->second);
    if(code->third != NULL)
        newCode->c = createSymbFromSsaSymb(code->third);  
    return newCode;
}

symb* createSymbFromSsaSymb(SsaSymb* var)
{
    symb* newSymb;
    switch(var->type)
    {
        case SYM_VAR:
        case SYM_ARRAY:
			newSymb = lookForVar(var);
			break;
        case SYM_FUNC:
			newSymb = lookForFunc(var);
			break;
        case SYM_LABEL:
			newSymb = lookForLabel(var);
            break;
        case SYM_TEXT:
			newSymb = create_symb(var->type,var->name,var->value);
            newSymb->label = var->label;
            break;
        case SYM_INT:
			newSymb = create_symb(var->type,var->name,var->value);
            break;
    }
    return newSymb;
}

symb* lookForVar(SsaSymb* var)
{
	unordered_map<string,symb*>::iterator it;
	it = s_varList.find(var->name);
	if(it != s_varList.end())
		return s_varList[var->name];
	symb* newSymb = create_symb(var->type,var->name,0);
	s_varList[newSymb->name] = newSymb;
	return newSymb;
} 

symb* lookForFunc(SsaSymb* var)
{
	unordered_map<string,symb*>::iterator it;
	it = s_funcList.find(var->name);
	if(it != s_funcList.end())
		return s_funcList[var->name];
	symb* newSymb = create_symb(var->type,var->name,0);
	s_funcList[newSymb->name] = newSymb;
	return newSymb;
}

symb* lookForLabel(SsaSymb* var)
{
	unordered_map<string,symb*>::iterator it;
	it = s_labelList.find(var->name);
	if(it != s_labelList.end())
		return s_labelList[var->name];
	symb* newSymb = create_symb(var->type,var->name,0);
	s_labelList[newSymb->name] = newSymb;
	return newSymb;
}

void clearFunc(void)
{
	s_funcList.clear();
}

void clearLabel(void)
{
	s_labelList.clear();
}

void clearVar(void)
{
	s_varList.clear();
}

void addNameToBlockName(string funcName)
{
	unordered_map<string,symb*>::iterator it;
	for(it = s_labelList.begin();it != s_labelList.end();it++)
	{
		string newName = funcName + "_" + it->second->name;
		strcpy(it->second->name,newName.c_str());
	}
}

#endif