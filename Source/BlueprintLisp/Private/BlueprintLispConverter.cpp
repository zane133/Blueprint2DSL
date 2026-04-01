// Copyright (c) 2026 OpenClaw Research. All Rights Reserved.
// BlueprintLispConverter.cpp - Blueprint EventGraph <-> BlueprintLisp DSL
//
// Export logic derived from ECABridge/ECABlueprintLispCommands.cpp (Epic Games, Experimental)
// Original author: Jon Olick
//
// This file implements the public FBlueprintLispConverter API.
// Import (DSL->BP) is currently stubbed; Export (BP->DSL) is fully implemented.

#include "BlueprintLispConverter.h"

#if WITH_EDITOR

#include "BlueprintLispAST.h"

#include "Engine/Blueprint.h"
#include "EdGraph/EdGraph.h"
#include "EdGraph/EdGraphNode.h"
#include "EdGraph/EdGraphPin.h"
#include "EdGraphSchema_K2.h"
#include "K2Node_Event.h"
#include "K2Node_CallFunction.h"
#include "K2Node_IfThenElse.h"
#include "K2Node_VariableGet.h"
#include "K2Node_VariableSet.h"
#include "K2Node_Self.h"
#include "K2Node_CustomEvent.h"
#include "K2Node_FunctionEntry.h"
#include "K2Node_FunctionResult.h"
#include "K2Node_MacroInstance.h"
#include "K2Node_DynamicCast.h"
#include "K2Node_ExecutionSequence.h"
#include "K2Node_Switch.h"
#include "K2Node_SwitchInteger.h"
#include "K2Node_SwitchString.h"
#include "K2Node_SwitchEnum.h"
#include "K2Node_InputAction.h"
#include "K2Node_InputKey.h"
#include "K2Node_ComponentBoundEvent.h"
#include "K2Node_ActorBoundEvent.h"
#include "K2Node_MakeArray.h"
#include "K2Node_GetArrayItem.h"
#include "K2Node_FunctionTerminator.h"
#include "Kismet2/BlueprintEditorUtils.h"
#include "Kismet2/KismetEditorUtilities.h"
#include "AssetRegistry/AssetRegistryModule.h"

DEFINE_LOG_CATEGORY_STATIC(LogBlueprintLisp, Log, All);

// ============================================================================
// Internal helpers: short-GUID generation for stable :id tags
// ============================================================================
namespace
{

/** Compute shortest unique GUID prefix for a set of GUIDs */
static TMap<FGuid, FString> ComputeShortIds(const TArray<FGuid>& Guids)
{
	static const int32 Lengths[] = { 8, 12, 16, 20, 32 };
	TMap<FGuid, FString> Result;
	if (Guids.IsEmpty()) return Result;

	for (int32 LenIdx = 0; LenIdx < UE_ARRAY_COUNT(Lengths); LenIdx++)
	{
		int32 Len = Lengths[LenIdx];
		TMap<FString, int32> PrefixCount;
		for (const FGuid& G : Guids)
		{
			FString S = G.ToString(EGuidFormats::Digits).Left(Len).ToLower();
			PrefixCount.FindOrAdd(S)++;
		}
		for (const FGuid& G : Guids)
		{
			if (Result.Contains(G)) continue;
			FString S = G.ToString(EGuidFormats::Digits).Left(Len).ToLower();
			if (PrefixCount[S] == 1)
				Result.Add(G, S);
		}
		bool bAllDone = true;
		for (const FGuid& G : Guids)
			if (!Result.Contains(G)) { bAllDone = false; break; }
		if (bAllDone) break;
	}
	// Fallback: full 32-char
	for (const FGuid& G : Guids)
		if (!Result.Contains(G))
			Result.Add(G, G.ToString(EGuidFormats::Digits).ToLower());
	return Result;
}

// ============================================================================
// Export: BP -> DSL
// ============================================================================

// Forward declarations
static FLispNodePtr ConvertPureExpressionToLisp(UEdGraphPin* ValuePin, UEdGraph* Graph, TSet<UEdGraphNode*>& Visited);
static FLispNodePtr ConvertNodeToLisp(UEdGraphNode* Node, UEdGraph* Graph, TSet<UEdGraphNode*>& Visited, bool bPositions, const TMap<FGuid, FString>& ShortIds);
static FLispNodePtr ConvertExecChainToLisp(UEdGraphPin* ExecPin, UEdGraph* Graph, TSet<UEdGraphNode*>& Visited, bool bPositions, const TMap<FGuid, FString>& ShortIds);

/** Append :id keyword to a form if the node has a stable GUID in ShortIds */
static FLispNodePtr AppendNodeId(FLispNodePtr Form, UEdGraphNode* Node, const TMap<FGuid, FString>& ShortIds)
{
	if (!Form.IsValid() || Form->IsNil() || !Form->IsList() || !Node) return Form;
	if (const FString* Id = ShortIds.Find(Node->NodeGuid))
	{
		Form->Children.Add(FLispNode::MakeKeyword(TEXT(":id")));
		Form->Children.Add(FLispNode::MakeString(*Id));
	}
	return Form;
}

/** Get clean function name from a K2Node_CallFunction */
static FString GetCleanNodeName(UEdGraphNode* Node)
{
	if (UK2Node_CallFunction* CF = Cast<UK2Node_CallFunction>(Node))
	{
		if (UFunction* Func = CF->GetTargetFunction())
			return Func->GetName();
	}
	return Node->GetNodeTitle(ENodeTitleType::ListView).ToString();
}

/** Find the "then" exec output pin of a node */
static UEdGraphPin* GetThenPin(UEdGraphNode* Node)
{
	for (UEdGraphPin* Pin : Node->Pins)
		if (Pin && Pin->Direction == EGPD_Output
			&& Pin->PinType.PinCategory == UEdGraphSchema_K2::PC_Exec
			&& Pin->PinName == UEdGraphSchema_K2::PN_Then)
			return Pin;
	// Fallback: first exec output
	for (UEdGraphPin* Pin : Node->Pins)
		if (Pin && Pin->Direction == EGPD_Output
			&& Pin->PinType.PinCategory == UEdGraphSchema_K2::PC_Exec)
			return Pin;
	return nullptr;
}

/** Map EdGraphPinType to a Lisp type symbol */
static FString PinTypeToLispType(const FEdGraphPinType& PT)
{
	FString Cat = PT.PinCategory.ToString();
	if (Cat == TEXT("bool"))   return TEXT("bool");
	if (Cat == TEXT("int"))    return TEXT("int");
	if (Cat == TEXT("int64"))  return TEXT("int64");
	if (Cat == TEXT("float") || Cat == TEXT("real") || Cat == TEXT("double")) return TEXT("float");
	if (Cat == TEXT("string")) return TEXT("string");
	if (Cat == TEXT("name"))   return TEXT("name");
	if (Cat == TEXT("text"))   return TEXT("text");
	if (Cat == TEXT("struct"))
	{
		if (PT.PinSubCategoryObject.IsValid())
			return PT.PinSubCategoryObject->GetName().ToLower();
		return TEXT("struct");
	}
	if (Cat == TEXT("object") || Cat == TEXT("class"))
	{
		if (PT.PinSubCategoryObject.IsValid())
			return PT.PinSubCategoryObject->GetName();
		return TEXT("object");
	}
	return Cat.ToLower();
}

// ----- Convert pure (data-flow) expression to Lisp -----
static FLispNodePtr ConvertPureExpressionToLisp(UEdGraphPin* ValuePin, UEdGraph* Graph, TSet<UEdGraphNode*>& Visited)
{
	if (!ValuePin || ValuePin->LinkedTo.Num() == 0)
	{
		// Return default value as literal
		if (!ValuePin || ValuePin->DefaultValue.IsEmpty()) return FLispNode::MakeNil();
		double Num = 0;
		if (ValuePin->PinType.PinCategory == UEdGraphSchema_K2::PC_Boolean)
			return FLispNode::MakeSymbol(ValuePin->DefaultValue.ToLower() == TEXT("true") ? TEXT("true") : TEXT("false"));
		if (ValuePin->PinType.PinCategory == UEdGraphSchema_K2::PC_Int
			|| ValuePin->PinType.PinCategory == UEdGraphSchema_K2::PC_Float
			|| ValuePin->PinType.PinCategory == UEdGraphSchema_K2::PC_Double
			|| ValuePin->PinType.PinCategory == UEdGraphSchema_K2::PC_Real)
		{
			if (LexTryParseString(Num, *ValuePin->DefaultValue))
				return FLispNode::MakeNumber(Num);
		}
		if (!ValuePin->DefaultValue.IsEmpty())
			return FLispNode::MakeString(ValuePin->DefaultValue);
		return FLispNode::MakeNil();
	}

	UEdGraphPin* SourcePin = ValuePin->LinkedTo[0];
	if (!SourcePin) return FLispNode::MakeNil();
	UEdGraphNode* SourceNode = SourcePin->GetOwningNode();
	if (!SourceNode) return FLispNode::MakeNil();

	// Variable get
	if (UK2Node_VariableGet* VarGet = Cast<UK2Node_VariableGet>(SourceNode))
	{
		FString VarName = VarGet->VariableReference.GetMemberName().ToString();
		if (VarGet->VariableReference.IsLocalScope())
			return FLispNode::MakeSymbol(VarName);
		// Member variable: (self.VarName)
		TArray<FLispNodePtr> Items;
		Items.Add(FLispNode::MakeSymbol(FString::Printf(TEXT("self.%s"), *VarName)));
		return FLispNode::MakeList(Items);
	}

	// Self node
	if (Cast<UK2Node_Self>(SourceNode))
		return FLispNode::MakeSymbol(TEXT("self"));

	// Literal function call (pure node)
	if (UK2Node_CallFunction* CallNode = Cast<UK2Node_CallFunction>(SourceNode))
	{
		if (CallNode->IsNodePure())
		{
			if (Visited.Contains(SourceNode)) return FLispNode::MakeSymbol(TEXT("...circular..."));
			Visited.Add(SourceNode);

			FString FuncName = GetCleanNodeName(SourceNode);
			TArray<FLispNodePtr> Args;
			Args.Add(FLispNode::MakeSymbol(FuncName));

			// Target object
			UEdGraphPin* SelfPin = SourceNode->FindPin(UEdGraphSchema_K2::PN_Self, EGPD_Input);
			if (SelfPin && SelfPin->LinkedTo.Num() > 0)
				Args.Add(ConvertPureExpressionToLisp(SelfPin, Graph, Visited));

			// Input data pins
			for (UEdGraphPin* Pin : SourceNode->Pins)
			{
				if (Pin->Direction != EGPD_Input) continue;
				if (Pin->PinType.PinCategory == UEdGraphSchema_K2::PC_Exec) continue;
				if (Pin->PinName == UEdGraphSchema_K2::PN_Self) continue;
				Args.Add(ConvertPureExpressionToLisp(Pin, Graph, Visited));
			}
			Visited.Remove(SourceNode);
			return FLispNode::MakeList(Args);
		}
	}

	// Default: return variable name or "?"
	return FLispNode::MakeSymbol(TEXT("?"));
}

// ----- Convert a single exec node to Lisp -----
static FLispNodePtr ConvertNodeToLisp(UEdGraphNode* Node, UEdGraph* Graph, TSet<UEdGraphNode*>& Visited, bool bPositions, const TMap<FGuid, FString>& ShortIds)
{
	if (!Node) return FLispNode::MakeNil();
	if (Visited.Contains(Node)) return FLispNode::MakeNil();
	Visited.Add(Node);

	// ---- branch ----
	if (UK2Node_IfThenElse* BranchNode = Cast<UK2Node_IfThenElse>(Node))
	{
		UEdGraphPin* CondPin  = BranchNode->GetConditionPin();
		UEdGraphPin* TruePin  = BranchNode->GetThenPin();
		UEdGraphPin* FalsePin = BranchNode->GetElsePin();

		TArray<FLispNodePtr> Args;
		Args.Add(FLispNode::MakeSymbol(TEXT("branch")));
		Args.Add(ConvertPureExpressionToLisp(CondPin, Graph, Visited));
		Args.Add(FLispNode::MakeKeyword(TEXT(":true")));
		Args.Add(ConvertExecChainToLisp(TruePin, Graph, Visited, bPositions, ShortIds));
		Args.Add(FLispNode::MakeKeyword(TEXT(":false")));
		Args.Add(ConvertExecChainToLisp(FalsePin, Graph, Visited, bPositions, ShortIds));
		return AppendNodeId(FLispNode::MakeList(Args), Node, ShortIds);
	}

	// ---- set variable ----
	if (UK2Node_VariableSet* VarSet = Cast<UK2Node_VariableSet>(Node))
	{
		FString VarName = VarSet->VariableReference.GetMemberName().ToString();
		UEdGraphPin* ValuePin = VarSet->FindPin(VarName, EGPD_Input);
		if (!ValuePin)
			for (UEdGraphPin* P : VarSet->Pins)
				if (P->Direction == EGPD_Input && P->PinType.PinCategory != UEdGraphSchema_K2::PC_Exec)
					{ ValuePin = P; break; }

		TArray<FLispNodePtr> Args;
		Args.Add(FLispNode::MakeSymbol(TEXT("set")));
		Args.Add(FLispNode::MakeSymbol(VarName));
		Args.Add(ConvertPureExpressionToLisp(ValuePin, Graph, Visited));
		return AppendNodeId(FLispNode::MakeList(Args), Node, ShortIds);
	}

	// ---- function call ----
	if (UK2Node_CallFunction* CallNode = Cast<UK2Node_CallFunction>(Node))
	{
		FString FuncName = GetCleanNodeName(Node);
		TArray<FLispNodePtr> Args;
		Args.Add(FLispNode::MakeSymbol(FuncName));

		// Target object (self pin)
		UEdGraphPin* SelfPin = Node->FindPin(UEdGraphSchema_K2::PN_Self, EGPD_Input);
		if (SelfPin && SelfPin->LinkedTo.Num() > 0)
			Args.Add(ConvertPureExpressionToLisp(SelfPin, Graph, Visited));

		// Input data pins
		for (UEdGraphPin* Pin : Node->Pins)
		{
			if (Pin->Direction != EGPD_Input) continue;
			if (Pin->PinType.PinCategory == UEdGraphSchema_K2::PC_Exec) continue;
			if (Pin->PinName == UEdGraphSchema_K2::PN_Self) continue;
			FLispNodePtr Val = ConvertPureExpressionToLisp(Pin, Graph, Visited);
			if (!Val->IsNil())
			{
				Args.Add(FLispNode::MakeKeyword(FString::Printf(TEXT(":%s"), *Pin->PinName.ToString().ToLower())));
				Args.Add(Val);
			}
		}

		// Output: wrap in (let result ...)
		TArray<FLispNodePtr> OutPins;
		for (UEdGraphPin* Pin : Node->Pins)
			if (Pin->Direction == EGPD_Output && Pin->PinType.PinCategory != UEdGraphSchema_K2::PC_Exec)
				OutPins.Add(FLispNode::MakeSymbol(Pin->PinName.ToString().ToLower()));

		if (OutPins.Num() == 1)
		{
			TArray<FLispNodePtr> Let;
			Let.Add(FLispNode::MakeSymbol(TEXT("let")));
			Let.Add(OutPins[0]);
			Let.Add(AppendNodeId(FLispNode::MakeList(Args), Node, ShortIds));
			return FLispNode::MakeList(Let);
		}

		return AppendNodeId(FLispNode::MakeList(Args), Node, ShortIds);
	}

	// ---- sequence ----
	if (UK2Node_ExecutionSequence* SeqNode = Cast<UK2Node_ExecutionSequence>(Node))
	{
		TArray<FLispNodePtr> Args;
		Args.Add(FLispNode::MakeSymbol(TEXT("seq")));
		for (UEdGraphPin* Pin : SeqNode->Pins)
		{
			if (Pin->Direction == EGPD_Output && Pin->PinType.PinCategory == UEdGraphSchema_K2::PC_Exec)
			{
				FLispNodePtr Body = ConvertExecChainToLisp(Pin, Graph, Visited, bPositions, ShortIds);
				if (Body.IsValid() && !Body->IsNil()) Args.Add(Body);
			}
		}
		return AppendNodeId(FLispNode::MakeList(Args), Node, ShortIds);
	}

	// ---- dynamic cast ----
	if (UK2Node_DynamicCast* CastNode = Cast<UK2Node_DynamicCast>(Node))
	{
		FString TypeName = CastNode->TargetType ? CastNode->TargetType->GetName() : TEXT("?");
		UEdGraphPin* ObjPin = CastNode->GetCastSourcePin();
		UEdGraphPin* SuccessPin = CastNode->GetValidCastPin();

		TArray<FLispNodePtr> Args;
		Args.Add(FLispNode::MakeSymbol(TEXT("cast")));
		Args.Add(FLispNode::MakeSymbol(TypeName));
		Args.Add(ConvertPureExpressionToLisp(ObjPin, Graph, Visited));
		FLispNodePtr SuccBody = ConvertExecChainToLisp(SuccessPin, Graph, Visited, bPositions, ShortIds);
		if (SuccBody.IsValid() && !SuccBody->IsNil()) Args.Add(SuccBody);
		return AppendNodeId(FLispNode::MakeList(Args), Node, ShortIds);
	}

	// ---- switch integer ----
	if (UK2Node_SwitchInteger* SwitchInt = Cast<UK2Node_SwitchInteger>(Node))
	{
		UEdGraphPin* SelPin = SwitchInt->GetSelectionPin();
		TArray<FLispNodePtr> Args;
		Args.Add(FLispNode::MakeSymbol(TEXT("switch-int")));
		Args.Add(ConvertPureExpressionToLisp(SelPin, Graph, Visited));
		for (UEdGraphPin* Pin : SwitchInt->Pins)
		{
			if (Pin->Direction == EGPD_Output && Pin->PinType.PinCategory == UEdGraphSchema_K2::PC_Exec
				&& Pin->PinName != TEXT("default"))
			{
				Args.Add(FLispNode::MakeKeyword(FString::Printf(TEXT(":%s"), *Pin->PinName.ToString())));
				Args.Add(ConvertExecChainToLisp(Pin, Graph, Visited, bPositions, ShortIds));
			}
		}
		UEdGraphPin* DefaultPin = SwitchInt->GetDefaultPin();
		if (DefaultPin)
		{
			Args.Add(FLispNode::MakeKeyword(TEXT(":default")));
			Args.Add(ConvertExecChainToLisp(DefaultPin, Graph, Visited, bPositions, ShortIds));
		}
		return AppendNodeId(FLispNode::MakeList(Args), Node, ShortIds);
	}

	// ---- fallback: generic call representation ----
	FString NodeLabel = Node->GetNodeTitle(ENodeTitleType::ListView).ToString()
		.Replace(TEXT(" "), TEXT("-")).ToLower();
	TArray<FLispNodePtr> FallbackArgs;
	FallbackArgs.Add(FLispNode::MakeSymbol(NodeLabel.IsEmpty() ? TEXT("node") : NodeLabel));
	return AppendNodeId(FLispNode::MakeList(FallbackArgs), Node, ShortIds);
}

// ----- Follow an exec chain and emit a Lisp form list -----
static FLispNodePtr ConvertExecChainToLisp(UEdGraphPin* ExecPin, UEdGraph* Graph, TSet<UEdGraphNode*>& Visited, bool bPositions, const TMap<FGuid, FString>& ShortIds)
{
	if (!ExecPin || ExecPin->LinkedTo.Num() == 0) return FLispNode::MakeNil();

	TArray<FLispNodePtr> Statements;
	UEdGraphPin* CurrentPin = ExecPin;

	while (CurrentPin && CurrentPin->LinkedTo.Num() > 0)
	{
		UEdGraphNode* NextNode = CurrentPin->LinkedTo[0]->GetOwningNode();
		if (!NextNode || Visited.Contains(NextNode)) break;

		FLispNodePtr NodeLisp = ConvertNodeToLisp(NextNode, Graph, Visited, bPositions, ShortIds);
		if (NodeLisp.IsValid() && !NodeLisp->IsNil())
			Statements.Add(NodeLisp);

		// branch terminates the chain (branches handled inside ConvertNodeToLisp)
		if (Cast<UK2Node_IfThenElse>(NextNode)) break;

		CurrentPin = GetThenPin(NextNode);
	}

	if (Statements.Num() == 0) return FLispNode::MakeNil();
	if (Statements.Num() == 1) return Statements[0];

	// Multiple statements: wrap in seq
	TArray<FLispNodePtr> Seq;
	Seq.Add(FLispNode::MakeSymbol(TEXT("seq")));
	Seq.Append(Statements);
	return FLispNode::MakeList(Seq);
}

// ----- Convert a standard K2Node_Event -----
static FLispNodePtr ConvertEventToLisp(UK2Node_Event* Event, UEdGraph* Graph, bool bPositions,
	const TMap<FGuid, FString>& ShortEventIds, const TMap<FGuid, FString>& ShortNodeIds)
{
	TSet<UEdGraphNode*> Visited;
	FString EventName = Event->EventReference.GetMemberName().ToString();
	if (EventName.IsEmpty()) EventName = Event->CustomFunctionName.ToString();
	if (EventName.IsEmpty()) EventName = Event->GetNodeTitle(ENodeTitleType::ListView).ToString();

	TArray<FLispNodePtr> EventArgs;
	EventArgs.Add(FLispNode::MakeSymbol(TEXT("event")));
	EventArgs.Add(FLispNode::MakeSymbol(EventName));

	// :event-id for stable identification
	if (const FString* EId = ShortEventIds.Find(Event->NodeGuid))
	{
		EventArgs.Add(FLispNode::MakeKeyword(TEXT(":event-id")));
		EventArgs.Add(FLispNode::MakeString(*EId));
	}

	// Position metadata
	if (bPositions)
	{
		EventArgs.Add(FLispNode::MakeKeyword(TEXT(":pos")));
		EventArgs.Add(FLispNode::MakeString(FString::Printf(TEXT("%d,%d"), Event->NodePosX, Event->NodePosY)));
	}

	// Exec output -> body
	UEdGraphPin* ThenPin = GetThenPin(Event);
	FLispNodePtr Body = ConvertExecChainToLisp(ThenPin, Graph, Visited, bPositions, ShortNodeIds);
	if (Body.IsValid() && !Body->IsNil())
	{
		if (Body->IsForm(TEXT("seq")))
		{
			for (int32 i = 1; i < Body->Num(); i++)
				EventArgs.Add(Body->Get(i));
		}
		else EventArgs.Add(Body);
	}

	return FLispNode::MakeList(EventArgs);
}

// ----- Convert a CustomEvent node -----
static FLispNodePtr ConvertCustomEventToLisp(UK2Node_CustomEvent* Event, UEdGraph* Graph, bool bPositions,
	const TMap<FGuid, FString>& ShortEventIds, const TMap<FGuid, FString>& ShortNodeIds)
{
	TSet<UEdGraphNode*> Visited;
	FString EventName = Event->CustomFunctionName.ToString();

	TArray<FLispNodePtr> EventArgs;
	EventArgs.Add(FLispNode::MakeSymbol(TEXT("event")));
	EventArgs.Add(FLispNode::MakeSymbol(EventName));

	if (const FString* EId = ShortEventIds.Find(Event->NodeGuid))
	{
		EventArgs.Add(FLispNode::MakeKeyword(TEXT(":event-id")));
		EventArgs.Add(FLispNode::MakeString(*EId));
	}

	// Parameters
	for (UEdGraphPin* Pin : Event->Pins)
	{
		if (Pin->Direction == EGPD_Output && Pin->PinType.PinCategory != UEdGraphSchema_K2::PC_Exec)
		{
			EventArgs.Add(FLispNode::MakeKeyword(TEXT(":param")));
			TArray<FLispNodePtr> ParamPair;
			ParamPair.Add(FLispNode::MakeSymbol(Pin->PinName.ToString()));
			ParamPair.Add(FLispNode::MakeSymbol(PinTypeToLispType(Pin->PinType)));
			EventArgs.Add(FLispNode::MakeList(ParamPair));
		}
	}

	UEdGraphPin* ThenPin = GetThenPin(Event);
	FLispNodePtr Body = ConvertExecChainToLisp(ThenPin, Graph, Visited, bPositions, ShortNodeIds);
	if (Body.IsValid() && !Body->IsNil())
	{
		if (Body->IsForm(TEXT("seq")))
			for (int32 i = 1; i < Body->Num(); i++) EventArgs.Add(Body->Get(i));
		else EventArgs.Add(Body);
	}

	return FLispNode::MakeList(EventArgs);
}

} // anonymous namespace

// ============================================================================
// FBlueprintLispConverter  (public API)
// ============================================================================

FBlueprintLispResult FBlueprintLispConverter::Export(
	UBlueprint* Blueprint,
	const FString& GraphName,
	const FExportOptions& Options)
{
	if (!Blueprint)
		return FBlueprintLispResult::Fail(TEXT("Blueprint is null"));

	// Find target graph
	UEdGraph* Graph = nullptr;
	for (UEdGraph* G : Blueprint->UbergraphPages)
		if (G && G->GetName() == GraphName) { Graph = G; break; }
	if (!Graph)
		for (UEdGraph* G : Blueprint->FunctionGraphs)
			if (G && G->GetName() == GraphName) { Graph = G; break; }
	if (!Graph)
		return FBlueprintLispResult::Fail(FString::Printf(TEXT("Graph '%s' not found in '%s'"), *GraphName, *Blueprint->GetName()));

	// Collect event nodes and build short IDs
	TArray<UK2Node_Event*>       Events;
	TArray<UK2Node_CustomEvent*> CustomEvents;
	TArray<FGuid> EventGuids, NodeGuids;

	for (UEdGraphNode* Node : Graph->Nodes)
	{
		if (UK2Node_CustomEvent* CE = Cast<UK2Node_CustomEvent>(Node)) { CustomEvents.Add(CE); EventGuids.Add(Node->NodeGuid); }
		else if (UK2Node_Event* E = Cast<UK2Node_Event>(Node))         { Events.Add(E);        EventGuids.Add(Node->NodeGuid); }
		else if (Node->NodeGuid.IsValid())                              { NodeGuids.Add(Node->NodeGuid); }
	}

	TMap<FGuid, FString> ShortEventIds = Options.bStableIds ? ComputeShortIds(EventGuids) : TMap<FGuid,FString>();
	TMap<FGuid, FString> ShortNodeIds  = Options.bStableIds ? ComputeShortIds(NodeGuids)  : TMap<FGuid,FString>();

	// Sort events for deterministic output
	Events.Sort([](const UK2Node_Event& A, const UK2Node_Event& B){
		return A.EventReference.GetMemberName().ToString() < B.EventReference.GetMemberName().ToString();
	});
	CustomEvents.Sort([](const UK2Node_CustomEvent& A, const UK2Node_CustomEvent& B){
		return A.CustomFunctionName.ToString() < B.CustomFunctionName.ToString();
	});

	// Generate Lisp forms
	TArray<FString> Forms;
	for (UK2Node_Event* E : Events)
	{
		FLispNodePtr Form = ConvertEventToLisp(E, Graph, Options.bIncludePositions, ShortEventIds, ShortNodeIds);
		if (Form.IsValid() && !Form->IsNil())
			Forms.Add(Form->ToString(Options.bPrettyPrint, 0));
	}
	for (UK2Node_CustomEvent* CE : CustomEvents)
	{
		FLispNodePtr Form = ConvertCustomEventToLisp(CE, Graph, Options.bIncludePositions, ShortEventIds, ShortNodeIds);
		if (Form.IsValid() && !Form->IsNil())
			Forms.Add(Form->ToString(Options.bPrettyPrint, 0));
	}

	if (Forms.IsEmpty())
		return FBlueprintLispResult::Fail(FString::Printf(TEXT("No events found in graph '%s'"), *GraphName));

	FString Code;
	for (int32 i = 0; i < Forms.Num(); i++)
	{
		if (i > 0) Code += TEXT("\n\n");
		Code += Forms[i];
	}

	return FBlueprintLispResult::Ok(Code);
}

FBlueprintLispResult FBlueprintLispConverter::ExportByPath(
	const FString& BlueprintPath,
	const FString& GraphName,
	const FExportOptions& Options)
{
	UBlueprint* BP = LoadObject<UBlueprint>(nullptr, *BlueprintPath);
	if (!BP)
		return FBlueprintLispResult::Fail(FString::Printf(TEXT("Failed to load Blueprint: %s"), *BlueprintPath));
	return Export(BP, GraphName, Options);
}

FBlueprintLispResult FBlueprintLispConverter::Validate(const FString& LispCode)
{
	FLispParseResult PR = FLispParser::Parse(LispCode);
	if (!PR.bSuccess)
		return FBlueprintLispResult::Fail(FString::Printf(TEXT("Parse error at %d:%d: %s"),
			PR.ErrorLine, PR.ErrorColumn, *PR.Error));

	for (const auto& Node : PR.Nodes)
	{
		if (!Node.IsValid() || !Node->IsList())
			return FBlueprintLispResult::Fail(TEXT("Top-level expressions must be lists"));
		FString Form = Node->GetFormName().ToLower();
		static const TSet<FString> ValidForms = {TEXT("event"),TEXT("func"),TEXT("macro"),TEXT("var"),TEXT("comment")};
		if (!ValidForms.Contains(Form))
			return FBlueprintLispResult::Fail(FString::Printf(TEXT("Unknown top-level form: %s"), *Form));
	}

	return FBlueprintLispResult::Ok(LispCode);
}

FBlueprintLispResult FBlueprintLispConverter::Import(
	UBlueprint* /*Blueprint*/,
	const FString& /*GraphName*/,
	const FString& /*LispCode*/,
	const FImportOptions& /*Options*/)
{
	// TODO: Import (DSL -> Blueprint) is a large undertaking (~5000 lines from ECABridge).
	// It will be implemented in a follow-up.
	return FBlueprintLispResult::Fail(TEXT("BlueprintLisp Import is not yet implemented. Use ECABridge lisp_to_blueprint command for now."));
}

FBlueprintLispResult FBlueprintLispConverter::ImportByPath(
	const FString& BlueprintPath,
	const FString& GraphName,
	const FString& LispCode,
	const FImportOptions& Options)
{
	UBlueprint* BP = LoadObject<UBlueprint>(nullptr, *BlueprintPath);
	if (!BP)
		return FBlueprintLispResult::Fail(FString::Printf(TEXT("Failed to load Blueprint: %s"), *BlueprintPath));
	return Import(BP, GraphName, LispCode, Options);
}

FBlueprintLispResult FBlueprintLispConverter::Update(
	UBlueprint* /*Blueprint*/,
	const FString& /*GraphName*/,
	const FString& /*NewLispCode*/,
	const FUpdateOptions& /*Options*/)
{
	// TODO: Incremental update via semantic diff (Phase 3 in ECABridge).
	return FBlueprintLispResult::Fail(TEXT("BlueprintLisp incremental Update is not yet implemented."));
}

UEdGraph* FBlueprintLispConverter::FindOrCreateGraph(UBlueprint* BP, const FString& GraphName)
{
	if (!BP) return nullptr;
	for (UEdGraph* G : BP->UbergraphPages)
		if (G && G->GetName() == GraphName) return G;
	for (UEdGraph* G : BP->FunctionGraphs)
		if (G && G->GetName() == GraphName) return G;
	return nullptr;
}

#endif // WITH_EDITOR
