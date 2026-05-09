with Ada.Text_IO; with Ada.Integer_Text_IO;

package body Universe with SPARK_Mode is

   procedure Init (U : out Universe) is
   begin
      --  TODO: implement
      raise Program_Error with "Init not yet implemented";
   end Init;

   procedure Add_Item
     (U   : in out Universe;
      pos : Spatial.Position;
      vel : Spatial.Velocity;
      rad : Big_Real)
   is
   begin
      --  TODO: implement
      raise Program_Error with "Add_Item not yet implemented";
   end Add_Item;

   procedure Reflect_Velocity_X
     (U : in out Universe; Index : Integer) is
   begin
      --  TODO: implement
      raise Program_Error with "Reflect_Velocity_X not yet implemented";
   end Reflect_Velocity_X;

   procedure Reflect_Velocity_Y
     (U : in out Universe; Index : Integer) is
   begin
      --  TODO: implement
      raise Program_Error with "Reflect_Velocity_Y not yet implemented";
   end Reflect_Velocity_Y;

   procedure Print (U : Universe)
     with SPARK_Mode => Off
   is
   begin
      for I in U.items'First .. U.item_count loop
         Ada.Text_IO.Put ("Item: ");
         Ada.Integer_Text_IO.Put (I);
         Ada.Text_IO.Put (": pos: (");
         Ada.Text_IO.Put
           (To_String (Spatial.Pos_X (U.items (I).pos)));
         Ada.Text_IO.Put (",");
         Ada.Text_IO.Put
           (To_String (Spatial.Pos_Y (U.items (I).pos)));
         Ada.Text_IO.Put (")");
         Ada.Text_IO.New_Line;
      end loop;
   end Print;

   procedure Tick (U : in out Universe) is
   begin
      --  TODO: implement
      raise Program_Error with "Tick not yet implemented";
   end Tick;

end Universe;
