// Copyright (c) 2026 OpenClaw Research. All Rights Reserved.
// BlueprintLispModule.h

#pragma once

#include "CoreMinimal.h"
#include "Modules/ModuleManager.h"

class BLUEPRINTLISP_API FBlueprintLispModule : public IModuleInterface
{
public:
	virtual void StartupModule()  override;
	virtual void ShutdownModule() override;

	static FBlueprintLispModule& Get()
	{
		return FModuleManager::GetModuleChecked<FBlueprintLispModule>("BlueprintLisp");
	}

	static bool IsAvailable()
	{
		return FModuleManager::Get().IsModuleLoaded("BlueprintLisp");
	}
};
