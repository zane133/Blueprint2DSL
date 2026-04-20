// Copyright (c) 2026 OpenClaw Research. All Rights Reserved.
// BlueprintLispModule.cpp

#include "BlueprintLispModule.h"
#include "FBlueprintLispMappingRegistry.h"
#include "BlueprintLispPythonBridge.h"
#include "Modules/ModuleManager.h"
#include "AssetRegistry/AssetData.h"
#include "ContentBrowserMenuContexts.h"
#include "Framework/Notifications/NotificationManager.h"
#include "Styling/AppStyle.h"
#include "Widgets/Notifications/SNotificationList.h"
#include "ToolMenus.h"

#define LOCTEXT_NAMESPACE "FBlueprintLispModule"

namespace BlueprintLispMenu
{
	static const FName SectionName(TEXT("BlueprintLisp"));
	static const FName EntryName(TEXT("BlueprintLisp.ConvertToDSL"));
}

void FBlueprintLispModule::StartupModule()
{
	UE_LOG(LogTemp, Log, TEXT("[BlueprintLisp] Module loaded."));

	// Initialize the MappingRegistry for default path resolution
	FBlueprintLispMappingRegistry::Get().Initialize();

	UToolMenus::RegisterStartupCallback(
		FSimpleMulticastDelegate::FDelegate::CreateRaw(this, &FBlueprintLispModule::RegisterContentBrowserMenu));
}

void FBlueprintLispModule::ShutdownModule()
{
	UnregisterContentBrowserMenu();

	UE_LOG(LogTemp, Log, TEXT("[BlueprintLisp] Module unloaded."));
}

void FBlueprintLispModule::RegisterContentBrowserMenu()
{
	FToolMenuOwnerScoped OwnerScoped(this);

	UToolMenu* Menu = UToolMenus::Get()->ExtendMenu(TEXT("ContentBrowser.AssetContextMenu.Blueprint"));
	if (!Menu)
	{
		return;
	}

	FToolMenuSection& Section = Menu->FindOrAddSection(BlueprintLispMenu::SectionName);
	Section.AddMenuEntry(
		BlueprintLispMenu::EntryName,
		LOCTEXT("ConvertBlueprintToDSL_Label", "转换蓝图成 DSL"),
		LOCTEXT("ConvertBlueprintToDSL_Tooltip", "将选中的 Blueprint 导出为 BlueprintLisp DSL 文件"),
		FSlateIcon(FAppStyle::GetAppStyleSetName(), "Kismet.Tabs.BlueprintDefaults"),
		FToolMenuExecuteAction::CreateLambda([](const FToolMenuContext& Context)
		{
			const UContentBrowserAssetContextMenuContext* AssetContext = Context.FindContext<UContentBrowserAssetContextMenuContext>();
			if (!AssetContext)
			{
				return;
			}

			for (const FAssetData& AssetData : AssetContext->SelectedAssets)
			{
				if (!AssetData.IsValid() || AssetData.AssetClassPath.GetAssetName() != TEXT("Blueprint"))
				{
					continue;
				}

				const FString BlueprintPath = AssetData.GetObjectPathString();
				const FString GraphName = TEXT("EventGraph");
				FBlueprintLispPythonResult Result = UBlueprintLispPythonBridge::ExportGraphToDefaultPath(BlueprintPath, GraphName, false, true);

				const bool bSuccess = Result.bSuccess;
				const FText NotifyText = bSuccess
					? FText::FromString(FString::Printf(TEXT("导出成功: %s"), *Result.FilePath))
					: FText::FromString(FString::Printf(TEXT("导出失败: %s"), *Result.Message));

				FNotificationInfo Info(NotifyText);
				Info.ExpireDuration = bSuccess ? 4.0f : 6.0f;
				Info.bUseLargeFont = false;
				Info.Image = bSuccess
					? FAppStyle::GetBrush(TEXT("Icons.SuccessWithColor"))
					: FAppStyle::GetBrush(TEXT("Icons.ErrorWithColor"));
				FSlateNotificationManager::Get().AddNotification(Info);

				if (bSuccess)
				{
					UE_LOG(LogTemp, Log, TEXT("[BlueprintLisp] %s"), *Result.Message);
				}
				else
				{
					UE_LOG(LogTemp, Error, TEXT("[BlueprintLisp] %s"), *Result.Message);
				}
			}
		}));
}

void FBlueprintLispModule::UnregisterContentBrowserMenu()
{
	if (!UToolMenus::TryGet())
	{
		return;
	}

	UToolMenus::UnRegisterStartupCallback(this);
	UToolMenus::UnregisterOwner(this);
}

#undef LOCTEXT_NAMESPACE

IMPLEMENT_MODULE(FBlueprintLispModule, BlueprintLisp)
